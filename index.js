/**
 * eclipse-ytmusic-addon — index.js
 *
 * Eclipse Music addon ported from the 8spine YouTube Music module
 * (https://github.com/nvmindl/8spine-ytmusic).
 *
 * Search:  YouTube Music internal WEB_REMIX API
 * Stream:  IOS client player API → HLS manifest (preferred) or direct mp4
 * Bot bypass: visitorData captured during search, forwarded to player
 *
 * No API key required. No TorBox. No Lidarr. Just YouTube Music.
 *
 * Install in Eclipse:
 *   http://localhost:3000/manifest.json
 *   (or your hosted URL)
 */

const express = require('express');
const cors    = require('cors');
const { execFile } = require('child_process');
const crypto = require('crypto');
const fs = require('fs/promises');
const fsSync = require('fs');
const os = require('os');
const path = require('path');
const { Readable } = require('stream');
const { promisify } = require('util');

const app = express();
app.use(cors());
app.use(express.json({ limit: '256kb' }));
app.use(express.urlencoded({ extended: false, limit: '256kb' }));
const execFileAsync = promisify(execFile);

// ─── Constants (identical to the 8spine module) ───────────────────────────────

const YTM_BASE    = 'https://music.youtube.com';
const YTM_API_KEY = 'AIzaSyC9XL3ZjWddXya6X74dJoCTL-WEYFDNX30';
const DOWNLOAD_API_BASE = 'https://capi.y2jar.cc/scr/';
const PUBLIC_MOUNT_PATHS = ['/ytmusic'];
const COOKIE_SESSION_FILE = process.env.COOKIE_SESSION_FILE || path.join(__dirname, '.cookie-sessions.json');
const OAUTH_CLIENT_ID = process.env.GOOGLE_OAUTH_CLIENT_ID || '';
const OAUTH_CLIENT_SECRET = process.env.GOOGLE_OAUTH_CLIENT_SECRET || '';
const ISSUE_TOKEN_CLIENT_ID = process.env.GOOGLE_ISSUE_TOKEN_CLIENT_ID || '936475272427.apps.googleusercontent.com';
const YOUTUBE_SCOPE = 'https://www.googleapis.com/auth/youtube';

const WEB_REMIX_CONTEXT = {
  clientName:    'WEB_REMIX',
  clientVersion: '1.20260304.03.00',
  hl: 'en',
  gl: 'US',
};

const IOS_CONTEXT = {
  clientName:    'IOS',
  clientVersion: '20.10.01',
  deviceMake:    'Apple',
  deviceModel:   'iPhone16,2',
  osName:        'iPhone',
  osVersion:     '18.3.2.22D82',
  hl: 'en',
};

// ─── In-memory visitorData cache ──────────────────────────────────────────────
// Captured from every WEB_REMIX search response and forwarded to the IOS
// player to pass YouTube's bot detection — same technique as the 8spine module.
const VISITOR_DATA_TTL_MS = 20 * 60 * 1000;
const URL_CACHE_TTL_MS = 10 * 60 * 1000;
const PROXY_URL_TTL_MS = 20 * 60 * 1000;
const COOKIE_SESSION_TTL_MS = 12 * 60 * 60 * 1000;
const TOKEN_SESSION_TTL_MS = 30 * 24 * 60 * 60 * 1000;
const PLAYER_TIMEOUT_MS = 5000;
const DOWNLOAD_API_TIMEOUT_MS = 6000;
const YT_DLP_UNAVAILABLE_TTL_MS = 5 * 60 * 1000;
let cachedVisitorData = null;
let cachedVisitorDataFetchedAt = 0;
const extractedUrlCache = new Map();
const proxiedUrlCache = new Map();
const cookieSessions = new Map();
let ytDlpUnavailableUntil = 0;

function saveCookieSessions() {
  const sessions = {};
  for (const [id, session] of cookieSessions.entries()) {
    sessions[id] = session;
  }

  const tmpFile = `${COOKIE_SESSION_FILE}.tmp`;
  fsSync.writeFileSync(tmpFile, JSON.stringify(sessions), { mode: 0o600 });
  fsSync.renameSync(tmpFile, COOKIE_SESSION_FILE);
}

function loadCookieSessions() {
  try {
    if (!fsSync.existsSync(COOKIE_SESSION_FILE)) return;
    const sessions = JSON.parse(fsSync.readFileSync(COOKIE_SESSION_FILE, 'utf8'));
    for (const [id, session] of Object.entries(sessions)) {
      if ((!session?.cookie && !session?.refreshToken && !session?.accessToken) || !session?.createdAt) continue;
      const ttl = (session.refreshToken || session.accessToken) ? TOKEN_SESSION_TTL_MS : COOKIE_SESSION_TTL_MS;
      if ((Date.now() - session.createdAt) < ttl) {
        cookieSessions.set(id, session);
      }
    }
  } catch (e) {
    console.warn('[cookie-session] Could not load saved sessions:', e.message);
  }
}

loadCookieSessions();

// ─── Helpers (identical logic to the 8spine module) ──────────────────────────

function parseDuration(text) {
  if (!text) return 0;
  const parts = text.split(':').map(Number);
  if (parts.length === 3) return parts[0] * 3600 + parts[1] * 60 + parts[2];
  if (parts.length === 2) return parts[0] * 60 + parts[1];
  return parts[0] || 0;
}

function getBaseUrl(req) {
  const configured = process.env.PUBLIC_BASE_URL;
  if (configured) return configured.replace(/\/+$/, '');

  const proto = req.get('x-forwarded-proto') || req.protocol;
  const host = req.get('x-forwarded-host') || req.get('host');
  const forwardedPrefix = (req.get('x-forwarded-prefix') || '').replace(/\/+$/, '');
  const detectedPrefix = PUBLIC_MOUNT_PATHS.find(prefix =>
    req.originalUrl === prefix || req.originalUrl.startsWith(`${prefix}/`)
  ) || '';
  const proxyStrippedPrefix = proto === 'https' && host === 'nvmindl.duckdns.org'
    ? PUBLIC_MOUNT_PATHS[0]
    : '';
  const prefix = forwardedPrefix || detectedPrefix || proxyStrippedPrefix;
  return `${proto}://${host}${prefix}`;
}

function getSessionBasePath(req) {
  return req.cookieSessionId ? `/u/${encodeURIComponent(req.cookieSessionId)}` : '';
}

function withStreamUrls(req, tracks) {
  return tracks;
}

function normalizeCookieHeader(rawCookie) {
  if (!rawCookie) return '';
  return String(rawCookie)
    .replace(/^cookie:\s*/i, '')
    .split(/\r?\n/)
    .map(line => line.trim())
    .filter(Boolean)
    .join('; ');
}

function getCookieValue(cookieHeader, name) {
  const escapedName = name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const match = String(cookieHeader || '').match(new RegExp(`(?:^|;\\s*)${escapedName}=([^;]+)`));
  return match ? decodeURIComponent(match[1]) : '';
}

function getSapisidAuthHeader(cookieHeader, origin) {
  const sapisid =
    getCookieValue(cookieHeader, 'SAPISID') ||
    getCookieValue(cookieHeader, '__Secure-1PAPISID') ||
    getCookieValue(cookieHeader, '__Secure-3PAPISID');
  if (!sapisid) return '';

  const timestamp = Math.floor(Date.now() / 1000);
  const hash = crypto
    .createHash('sha1')
    .update(`${timestamp} ${sapisid} ${origin}`)
    .digest('hex');
  return `SAPISIDHASH ${timestamp}_${hash}`;
}

function normalizeRefreshToken(rawToken) {
  return String(rawToken || '')
    .trim()
    .replace(/^authorization:\s*bearer\s+/i, '')
    .replace(/^bearer\s+/i, '');
}

function stringifyProviderError(value) {
  if (!value) return '';
  if (typeof value === 'string') return value;
  if (value.message) return value.message;
  if (value.error_description) return value.error_description;
  if (value.error) return stringifyProviderError(value.error);
  try {
    return JSON.stringify(value);
  } catch {
    return String(value);
  }
}

function makeProviderError(prefix, data, status) {
  const details = stringifyProviderError(data);
  return new Error(details ? `${prefix}: ${details}` : `${prefix}: HTTP ${status}`);
}

async function exchangeRefreshTokenViaOAuth(refreshToken) {
  if (!OAUTH_CLIENT_ID || !OAUTH_CLIENT_SECRET) {
    throw new Error('OAuth client credentials are not configured');
  }

  const body = new URLSearchParams({
    client_id: OAUTH_CLIENT_ID,
    client_secret: OAUTH_CLIENT_SECRET,
    refresh_token: refreshToken,
    grant_type: 'refresh_token',
  });

  const response = await fetch('https://oauth2.googleapis.com/token', {
    method: 'POST',
    headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
    body,
    signal: AbortSignal.timeout(8000),
  });
  const text = await response.text();
  const data = JSON.parse(text || '{}');
  if (!response.ok || !data.access_token) {
    throw makeProviderError('OAuth refresh failed', data, response.status);
  }
  return data;
}

async function exchangeRefreshTokenViaIssueToken(refreshToken, hl = 'en') {
  const body = new URLSearchParams({
    client_id: ISSUE_TOKEN_CLIENT_ID,
    device_id: crypto.randomBytes(16).toString('hex'),
    hl,
    lib_ver: '3.3',
    passcode_present: 'YES',
    response_type: 'token',
    scope: YOUTUBE_SCOPE,
  });

  const response = await fetch('https://oauthaccountmanager.googleapis.com/v1/issuetoken', {
    method: 'POST',
    headers: {
      'Accept': '*/*',
      'Authorization': `Bearer ${refreshToken}`,
      'Content-Type': 'application/x-www-form-urlencoded',
      'User-Agent': 'com.google.ios.youtubemusic/7.29.1 iPhone/18.3.2 hw/iPhone16_2',
    },
    body,
    signal: AbortSignal.timeout(8000),
  });
  const text = await response.text();
  let data;
  try {
    data = JSON.parse(text || '{}');
  } catch {
    data = Object.fromEntries(new URLSearchParams(text));
  }

  const accessToken = data.access_token || data.token || data.auth_token;
  if (!response.ok || !accessToken) {
    throw makeProviderError('IssueToken failed', data || text, response.status);
  }
  return {
    access_token: accessToken,
    expires_in: Number(data.expires_in || data.expiresIn || 3600),
    token_type: data.token_type || data.tokenType || 'Bearer',
    scope: data.scope || YOUTUBE_SCOPE,
  };
}

async function refreshAccessToken(session, force = false) {
  if (!session?.refreshToken) return null;
  if (!force && session.accessToken && session.accessTokenExpiresAt > (Date.now() + 60_000)) {
    return session.accessToken;
  }

  let data;
  try {
    data = await exchangeRefreshTokenViaOAuth(session.refreshToken);
    session.tokenSource = 'oauth';
  } catch (oauthError) {
    data = await exchangeRefreshTokenViaIssueToken(session.refreshToken, session.hl || 'en');
    session.tokenSource = 'issuetoken';
    session.lastOAuthError = oauthError.message;
  }

  session.accessToken = data.access_token;
  session.accessTokenExpiresAt = Date.now() + (Number(data.expires_in || 3600) * 1000);
  session.lastUsedAt = Date.now();
  saveCookieSessions();
  return session.accessToken;
}

function createCookieSession(rawCookie) {
  const cookie = normalizeCookieHeader(rawCookie);
  if (!cookie) throw new Error('Cookie is required');
  if (!/[A-Za-z0-9_.-]+=/.test(cookie)) {
    throw new Error('Paste the full browser Cookie header, not a single token. It should contain name=value pairs separated by semicolons.');
  }

  const id = crypto.randomUUID();
  cookieSessions.set(id, {
    cookie,
    createdAt: Date.now(),
    lastUsedAt: Date.now(),
  });
  saveCookieSessions();
  return id;
}

async function createTokenSession(rawToken, gl = 'US', hl = 'en') {
  const refreshToken = normalizeRefreshToken(rawToken);
  if (!refreshToken) throw new Error('Refresh token is required');
  if (!/^1\/\//.test(refreshToken) && !/^ya29\./.test(refreshToken)) {
    throw new Error('Paste the token that starts with 1// from the YouTube Music mobile setup.');
  }

  const id = crypto.randomUUID();
  const session = {
    gl: String(gl || 'US').trim().toUpperCase().slice(0, 2) || 'US',
    hl: String(hl || 'en').trim().slice(0, 12) || 'en',
    createdAt: Date.now(),
    lastUsedAt: Date.now(),
  };

  if (/^ya29\./.test(refreshToken)) {
    session.accessToken = refreshToken;
    session.accessTokenExpiresAt = Date.now() + (45 * 60 * 1000);
    session.tokenSource = 'access-token';
  } else {
    session.refreshToken = refreshToken;
    try {
      await refreshAccessToken(session, true);
    } catch (e) {
      // Tokens captured from the YouTube Music mobile app can be bound to
      // Google's own OAuth client. If exchange is blocked, keep it as the
      // bearer token and let the private addon test it directly.
      session.accessToken = refreshToken;
      session.accessTokenExpiresAt = Date.now() + (45 * 60 * 1000);
      session.tokenSource = 'raw-bearer';
      session.lastTokenExchangeError = e.message;
    }
  }

  cookieSessions.set(id, session);
  saveCookieSessions();
  return id;
}

function getCookieSession(id) {
  if (!id) return null;
  const session = cookieSessions.get(id);
  if (!session) return null;
  const ttl = (session.refreshToken || session.accessToken) ? TOKEN_SESSION_TTL_MS : COOKIE_SESSION_TTL_MS;
  if ((Date.now() - session.createdAt) >= ttl) {
    cookieSessions.delete(id);
    saveCookieSessions();
    return null;
  }
  session.lastUsedAt = Date.now();
  saveCookieSessions();
  return session;
}

function getSessionOptions(req) {
  return {
    cookie: req.cookieSession?.cookie || null,
    accessToken: req.cookieSession?.accessToken || null,
    refreshToken: req.cookieSession?.refreshToken || null,
    tokenSession: req.cookieSession || null,
    gl: req.cookieSession?.gl || null,
    hl: req.cookieSession?.hl || null,
  };
}

async function addAccountAuth(headers, options = {}) {
  if (options.tokenSession?.refreshToken && options.tokenSession.tokenSource !== 'raw-bearer') {
    const accessToken = await refreshAccessToken(options.tokenSession);
    if (accessToken) {
      headers.Authorization = `Bearer ${accessToken}`;
      headers['X-Goog-AuthUser'] = '0';
      headers['X-Origin'] = YTM_BASE;
    }
  }
  if (!headers.Authorization && options.accessToken) {
    headers.Authorization = `Bearer ${options.accessToken}`;
    headers['X-Goog-AuthUser'] = '0';
    headers['X-Origin'] = YTM_BASE;
  }
  if (options.cookie) {
    headers.Cookie = options.cookie;
    headers['X-Goog-AuthUser'] = '0';
    headers['X-Origin'] = YTM_BASE;
    const authHeader = getSapisidAuthHeader(options.cookie, YTM_BASE);
    if (authHeader) headers.Authorization = authHeader;
  }
  return headers;
}

function requireCookieSession(req, res, next) {
  const session = getCookieSession(req.params.sessionId);
  if (!session) {
    return res.status(404).json({
      error: 'Cookie session not found or expired. Create a new one at /cookie.',
    });
  }
  req.cookieSessionId = req.params.sessionId;
  req.cookieSession = session;
  next();
}

function manifestResponse(req) {
  const baseUrl = getBaseUrl(req);
  const setupPageUrl = `${baseUrl}/setup`;
  const sessionKind = req.cookieSession?.refreshToken ? 'account-token' : 'cookie';
  const description = req.cookieSessionId
    ? `Stream YouTube Music with your private ${sessionKind} session.`
    : `Stream YouTube Music in Eclipse. Create a private account-token install URL at ${setupPageUrl}.`;

  return {
    id:          req.cookieSessionId ? `com.nvmindl.eclipse-ytmusic.${req.cookieSessionId}` : 'com.nvmindl.eclipse-ytmusic',
    name:        'YouTube Music',
    version:     '4.1.0-eclipse.1',
    description,
    icon:        'https://music.youtube.com/img/favicon_144.png',
    resources:   ['search', 'stream', 'catalog'],
    types:       ['track', 'album'],
    contentType: 'music',
  };
}

function setupPageHtml(req, installUrl = '', error = '') {
  const baseUrl = getBaseUrl(req);
  return `<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>YouTube Music Eclipse Setup</title>
  <style>
    body { margin: 0; font-family: system-ui, -apple-system, Segoe UI, sans-serif; background: #101114; color: #f5f5f5; }
    main { width: min(780px, calc(100% - 32px)); margin: 44px auto; }
    label, textarea, button, input, select { display: block; width: 100%; box-sizing: border-box; }
    textarea, input, select { margin-top: 8px; border: 1px solid #3a3d45; border-radius: 8px; background: #181a20; color: #f5f5f5; padding: 12px; }
    textarea { min-height: 150px; resize: vertical; font-family: ui-monospace, SFMono-Regular, Consolas, monospace; }
    button { margin-top: 16px; border: 0; border-radius: 8px; background: #2da7df; color: white; padding: 12px 14px; font-weight: 700; cursor: pointer; }
    p, li { color: #c5c7ce; line-height: 1.55; }
    .grid { display: grid; grid-template-columns: 1fr 1fr; gap: 12px; }
    .result, .error { margin-top: 24px; padding: 16px; border-radius: 8px; }
    .result { background: #18251d; border: 1px solid #2f6f43; }
    .error { background: #2a1719; border: 1px solid #8f3440; }
    code { overflow-wrap: anywhere; }
    a { color: #7dd3fc; }
    @media (max-width: 640px) { .grid { grid-template-columns: 1fr; } }
  </style>
</head>
<body>
  <main>
    <h1>YouTube Music Eclipse Setup</h1>
    <p>This creates a private Eclipse addon URL using the account token style used by the working YouTube Music addon flow. Paste the token that starts with <code>1//</code>; do not paste it into the browser address bar.</p>
    <form method="post" action="${baseUrl}/api/setup">
      <label for="refreshToken">YouTube Music account token</label>
      <textarea id="refreshToken" name="refreshToken" autocomplete="off" spellcheck="false" placeholder="1//0..."></textarea>
      <div class="grid">
        <label>Country
          <input name="gl" value="SA" maxlength="2">
        </label>
        <label>Language
          <input name="hl" value="en">
        </label>
      </div>
      <button type="submit">Create Eclipse install URL</button>
    </form>
    <p>Cookie fallback is still available at <a href="${baseUrl}/cookie">${baseUrl}/cookie</a>, but account-token setup is the path we should test now.</p>
    ${installUrl ? `<div class="result"><strong>Install URL</strong><p><code>${installUrl}</code></p></div>` : ''}
    ${error ? `<div class="error">${error}</div>` : ''}
  </main>
</body>
</html>`;
}

function cookiePageHtml(req, installUrl = '', error = '') {
  const baseUrl = getBaseUrl(req);
  return `<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>YouTube Music Cookie Session</title>
  <style>
    body { margin: 0; font-family: system-ui, -apple-system, Segoe UI, sans-serif; background: #101114; color: #f5f5f5; }
    main { width: min(760px, calc(100% - 32px)); margin: 48px auto; }
    label, textarea, button, input { display: block; width: 100%; box-sizing: border-box; }
    textarea, input { margin-top: 8px; border: 1px solid #3a3d45; border-radius: 8px; background: #181a20; color: #f5f5f5; padding: 12px; }
    textarea { min-height: 180px; resize: vertical; font-family: ui-monospace, SFMono-Regular, Consolas, monospace; }
    button { margin-top: 16px; border: 0; border-radius: 8px; background: #ff355d; color: white; padding: 12px 14px; font-weight: 700; cursor: pointer; }
    p { color: #c5c7ce; line-height: 1.55; }
    .result, .error { margin-top: 24px; padding: 16px; border-radius: 8px; }
    .result { background: #18251d; border: 1px solid #2f6f43; }
    .error { background: #2a1719; border: 1px solid #8f3440; }
    code { overflow-wrap: anywhere; }
  </style>
</head>
<body>
  <main>
    <h1>YouTube Music Cookie Session</h1>
    <p>Paste a YouTube Music cookie to generate a private Eclipse install URL. The cookie is kept in server memory only and expires after 12 hours or when the server restarts.</p>
    <form method="post" action="cookie">
      <label for="cookie">Cookie header</label>
      <textarea id="cookie" name="cookie" autocomplete="off" spellcheck="false" placeholder="VISITOR_INFO1_LIVE=...; __Secure-1PSID=..."></textarea>
      <button type="submit">Create install URL</button>
    </form>
    ${installUrl ? `<div class="result"><strong>Install URL</strong><p><code>${installUrl}</code></p></div>` : ''}
    ${error ? `<div class="error">${error}</div>` : ''}
  </main>
</body>
</html>`;
}

function bestThumbnail(thumbnails) {
  if (!thumbnails || !thumbnails.length) return '';
  return thumbnails.reduce((best, t) =>
    (t.width || 0) > (best.width || 0) ? t : best
  ).url;
}

function parseInfoRuns(runs) {
  if (!runs || !runs.length) return { artist: '', album: '' };
  const parts = [];
  let current = '';
  for (const run of runs) {
    if (run.text === ' \u2022 ') {
      if (current) parts.push(current.trim());
      current = '';
    } else {
      current += run.text;
    }
  }
  if (current) parts.push(current.trim());
  // Strip trailing duration strings like "4:51" or "1:23:45"
  while (parts.length > 1 && /^\d+:\d{2}(:\d{2})?$/.test(parts[parts.length - 1])) {
    parts.pop();
  }
  const typeLabels = ['Song', 'Video', 'EP', 'Single', 'Podcast'];
  let idx = 0;
  if (parts.length > 1 && typeLabels.includes(parts[0])) idx = 1;
  return { artist: parts[idx] || '', album: parts[idx + 1] || '' };
}

// ─── Core functions (ported directly from the 8spine module) ─────────────────

async function searchYTMusic(query, limit = 20, options = {}) {
  const headers = {
    'Content-Type': 'application/json',
    'Origin':       YTM_BASE,
    'Referer':      YTM_BASE + '/',
    'User-Agent':   'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
  };
  await addAccountAuth(headers, options);
  const client = {
    ...WEB_REMIX_CONTEXT,
    ...(options.hl ? { hl: options.hl } : {}),
    ...(options.gl ? { gl: options.gl } : {}),
  };

  const response = await fetch(`${YTM_BASE}/youtubei/v1/search?key=${YTM_API_KEY}`, {
    method: 'POST',
    headers,
    body: JSON.stringify({
      context: { client },
      query,
      params: 'EgWKAQIIAWoKEAkQBRAKEAMQBA%3D%3D', // filter: songs
    }),
  });

  const data = await response.json();

      // Cache visitorData for the player bot-bypass
      if (data?.responseContext?.visitorData) {
        cachedVisitorData = data.responseContext.visitorData;
        cachedVisitorDataFetchedAt = Date.now();
      }

  const tracks = [];
  const sections =
    data?.contents?.tabbedSearchResultsRenderer?.tabs?.[0]
      ?.tabRenderer?.content?.sectionListRenderer?.contents || [];

  for (const section of sections) {
    const shelf = section.musicShelfRenderer;
    if (!shelf) continue;
    for (const item of (shelf.contents || [])) {
      if (tracks.length >= limit) break;
      const r = item.musicResponsiveListItemRenderer;
      if (!r) continue;

      const videoId =
        r.playlistItemData?.videoId ||
        r.overlay?.musicItemThumbnailOverlayRenderer?.content
          ?.musicPlayButtonRenderer?.playNavigationEndpoint
          ?.watchEndpoint?.videoId;
      if (!videoId) continue;

      const title =
        r.flexColumns?.[0]?.musicResponsiveListItemFlexColumnRenderer
          ?.text?.runs?.map(t => t.text).join('') || '';
      const infoRuns =
        r.flexColumns?.[1]?.musicResponsiveListItemFlexColumnRenderer
          ?.text?.runs || [];
      const info         = parseInfoRuns(infoRuns);
      const durationText =
        r.fixedColumns?.[0]?.musicResponsiveListItemFixedColumnRenderer
          ?.text?.runs?.[0]?.text || '';
      const thumbs =
        r.thumbnail?.musicThumbnailRenderer?.thumbnail?.thumbnails || [];

      tracks.push({
        id:         videoId,
        title,
        artist:     info.artist,
        album:      info.album,
        duration:   parseDuration(durationText),
        artworkURL: bestThumbnail(thumbs),
        albumCover: bestThumbnail(thumbs),
        format:     'aac', // HLS/mp4 audio from YouTube
      });
    }
  }

  return tracks;
}

async function searchYTMusicWithFallback(query, limit = 20, options = {}) {
  const tracks = await searchYTMusic(query, limit, options);
  if (tracks.length || (!options.cookie && !options.refreshToken && !options.accessToken)) {
    return tracks;
  }

  console.warn('[search] Account-auth search returned no tracks, retrying anonymous search for:', query);
  return searchYTMusic(query, limit);
}

async function getVisitorData(options = {}) {
  if (options.cookie) return cachedVisitorData;
  if (cachedVisitorData && (Date.now() - cachedVisitorDataFetchedAt) < VISITOR_DATA_TTL_MS) {
    return cachedVisitorData;
  }
  try {
    const resp = await fetch(`${YTM_BASE}/youtubei/v1/visitor_id?key=${YTM_API_KEY}`, {
      method:  'POST',
      headers: { 'Content-Type': 'application/json' },
      body:    JSON.stringify({ context: { client: WEB_REMIX_CONTEXT } }),
    });
    if (!resp.ok) throw new Error('HTTP ' + resp.status);
    const d = await resp.json();
    if (d?.responseContext?.visitorData) {
      cachedVisitorData = d.responseContext.visitorData;
      cachedVisitorDataFetchedAt = Date.now();
      console.log('[YTMusic] visitorData refreshed');
    }
  } catch (e) {
    console.warn('[YTMusic] visitorData fetch failed:', e.message);
  }
  return cachedVisitorData;
}

function pickDirectAudioFormat(formats, quality) {
  const directFormats = (formats || [])
    .filter(f =>
      f.url &&
      (
        f.mimeType?.startsWith('audio/mp4') ||
        f.mimeType?.startsWith('audio/webm') ||
        f.mimeType?.startsWith('audio/ogg')
      )
    );

  if (directFormats.length === 0) return null;

  directFormats.sort((a, b) => {
    const aIsMp4 = a.mimeType?.startsWith('audio/mp4') ? 1 : 0;
    const bIsMp4 = b.mimeType?.startsWith('audio/mp4') ? 1 : 0;
    return (bIsMp4 - aIsMp4) || ((b.bitrate || 0) - (a.bitrate || 0));
  });
  return quality === 'low'
    ? directFormats[directFormats.length - 1]
    : directFormats[0];
}

function formatFromMimeType(mimeType = '') {
  if (mimeType.includes('audio/mp4')) return 'm4a';
  if (mimeType.includes('audio/webm')) return 'ogg';
  if (mimeType.includes('audio/ogg')) return 'ogg';
  return 'aac';
}

function getCachedExtractedUrl(cacheKey) {
  const entry = extractedUrlCache.get(cacheKey);
  if (!entry) return null;
  if ((Date.now() - entry.createdAt) >= URL_CACHE_TTL_MS) {
    extractedUrlCache.delete(cacheKey);
    return null;
  }
  return entry.value;
}

function setCachedExtractedUrl(cacheKey, value) {
  extractedUrlCache.set(cacheKey, {
    createdAt: Date.now(),
    value,
  });
}

function setProxiedUrl(value) {
  const token = crypto.randomUUID();
  proxiedUrlCache.set(token, {
    createdAt: Date.now(),
    value,
  });
  return token;
}

function getProxiedUrl(token) {
  const entry = proxiedUrlCache.get(token);
  if (!entry) return null;
  if ((Date.now() - entry.createdAt) >= PROXY_URL_TTL_MS) {
    proxiedUrlCache.delete(token);
    return null;
  }
  return entry.value;
}

function proxiedPlaybackResult(req, result) {
  const token = setProxiedUrl(result);
  const sessionBasePath = getSessionBasePath(req);
  return {
    ...result,
    url: `${getBaseUrl(req)}${sessionBasePath}/stream-proxy-token/${encodeURIComponent(token)}.m4a`,
  };
}

async function resolvePlaybackForEclipse(req, videoId, options = {}) {
  const result = await resolveDownload(videoId, '320', {
    ...options,
    skipStream: true,
  });
  return {
    ...proxiedPlaybackResult(req, result),
    format: 'm4a',
    quality: result.quality || '128kbps',
    duration: result.duration || 0,
    durationMs: result.durationMs || (result.duration ? result.duration * 1000 : 0),
  };
}

async function proxyAudioResponse(req, res, result) {
  const upstreamHeaders = {};
  if (req.headers.range) upstreamHeaders.Range = req.headers.range;

  const upstream = await fetch(result.url, { headers: upstreamHeaders });
  if (!upstream.ok && upstream.status !== 206) {
    res.status(upstream.status).send(await upstream.text().catch(() => 'Upstream audio failed'));
    return;
  }

  res.status(upstream.status);
  const passthroughHeaders = [
    'content-type',
    'content-length',
    'accept-ranges',
    'content-range',
    'cache-control',
    'last-modified',
    'etag',
  ];
  for (const header of passthroughHeaders) {
    const value = upstream.headers.get(header);
    if (value) res.setHeader(header, value);
  }
  if (!upstream.headers.get('content-type') && result.contentType) {
    res.setHeader('Content-Type', result.contentType);
  }
  res.setHeader('Access-Control-Allow-Origin', '*');

  if (!upstream.body) {
    res.end();
    return;
  }
  Readable.fromWeb(upstream.body).pipe(res);
}

async function streamProxyAudio(req, res, videoId, options = {}) {
  try {
    const result = await resolveStream(videoId, 'high', {
      ...options,
      directOnly: true,
    });
    await proxyAudioResponse(req, res, result);
  } catch (streamError) {
    try {
      const result = await resolveDownload(videoId, '320', {
        ...options,
        skipStream: true,
      });
      await proxyAudioResponse(req, res, result);
    } catch (fallbackError) {
      if (options.cookie || options.refreshToken || options.accessToken) {
        try {
          console.warn('[stream-proxy]', videoId, 'account-auth failed, retrying anonymous:', fallbackError.message);
          return await streamProxyAudio(req, res, videoId);
        } catch (anonymousError) {
          console.error('[stream-proxy-anon]', videoId, anonymousError.message);
        }
      }
      console.error('[stream-proxy]', videoId, streamError.message);
      console.error('[stream-proxy-fallback]', videoId, fallbackError.message);
      res.status(500).json({ error: fallbackError.message });
    }
  }
}

function getProxyVideoId(rawId = '') {
  return rawId.replace(/\.m4a$/i, '');
}

function cookieHeaderToNetscape(cookieHeader) {
  const rows = ['# Netscape HTTP Cookie File'];
  const cookies = cookieHeader
    .split(';')
    .map(part => part.trim())
    .filter(Boolean)
    .map(part => {
      const index = part.indexOf('=');
      if (index <= 0) return null;
      return {
        name: part.slice(0, index).trim(),
        value: part.slice(index + 1).trim(),
      };
    })
    .filter(cookie => cookie && cookie.name && cookie.value);

  for (const domain of ['.youtube.com', '.google.com']) {
    for (const cookie of cookies) {
      rows.push([domain, 'TRUE', '/', 'TRUE', '0', cookie.name, cookie.value].join('\t'));
    }
  }

  return rows.join('\n') + '\n';
}

async function writeTempYtDlpCookieFile(cookieHeader) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'ytmusic-cookies-'));
  const file = path.join(dir, 'cookies.txt');
  await fs.writeFile(file, cookieHeaderToNetscape(cookieHeader), { mode: 0o600 });
  return { dir, file };
}

async function resolveWithYtDlp(videoId, quality = 'high', options = {}) {
  const cacheKey = `${videoId}:${quality}:${options.cookie ? 'cookie' : options.accessToken ? 'token' : 'anon'}`;
  const cached = getCachedExtractedUrl(cacheKey);
  if (cached) return cached;
  if (Date.now() < ytDlpUnavailableUntil) {
    throw new Error('yt-dlp unavailable');
  }

  const formatSelector = quality === 'low'
    ? 'bestaudio[abr<=128][ext=m4a]/bestaudio[abr<=128]/bestaudio[ext=m4a]/bestaudio'
    : 'bestaudio[ext=m4a]/bestaudio';

  const ytDlpCommands = [
    { file: path.join(__dirname, 'bin', process.platform === 'win32' ? 'yt-dlp.exe' : 'yt-dlp'), args: [] },
    { file: 'yt-dlp', args: [] },
    { file: 'python3', args: ['-m', 'yt_dlp'] },
    { file: 'python', args: ['-m', 'yt_dlp'] },
    { file: 'py', args: ['-m', 'yt_dlp'] },
  ];

  let stdout = '';
  let lastError = null;
  const cookieTemp = options.cookie ? await writeTempYtDlpCookieFile(options.cookie) : null;
  try {
    for (const command of ytDlpCommands) {
      try {
        const result = await execFileAsync(
          command.file,
          [
            ...command.args,
            ...(process.platform !== 'win32' && fsSync.existsSync('/usr/bin/node')
              ? ['--js-runtimes', 'node:/usr/bin/node']
              : []),
            '--no-playlist',
            '--get-url',
            '--format',
            formatSelector,
            ...(options.accessToken ? ['--add-header', `Authorization: Bearer ${options.accessToken}`] : []),
            ...(cookieTemp ? ['--cookies', cookieTemp.file] : []),
            `https://music.youtube.com/watch?v=${videoId}`,
          ],
          { timeout: options.cookie ? 15000 : 5000, maxBuffer: 1024 * 1024 }
        );
        stdout = result.stdout;
        break;
      } catch (e) {
        lastError = e;
        const message = (e.stderr || e.message || '').trim();
        if (!message.includes('ENOENT') && !message.includes('No module named yt_dlp')) {
          break;
        }
      }
    }
  } finally {
    if (cookieTemp) {
      await fs.rm(cookieTemp.dir, { recursive: true, force: true }).catch(() => {});
    }
  }

  if (!stdout && lastError) {
    const message = (lastError.stderr || lastError.message).trim();
    if (message.includes('ENOENT') || message.includes('No module named yt_dlp')) {
      ytDlpUnavailableUntil = Date.now() + YT_DLP_UNAVAILABLE_TTL_MS;
      throw new Error('yt-dlp unavailable: ' + message);
    }
    throw new Error('yt-dlp failed: ' + message);
  }

  const url = stdout.split(/\r?\n/).map(line => line.trim()).find(Boolean);
  if (!url) throw new Error('yt-dlp returned no URL');

  const result = {
    url,
    format: url.includes('mime=audio%2Fmp4') ? 'm4a' : 'ogg',
    quality,
  };
  setCachedExtractedUrl(cacheKey, result);
  return result;
}

async function resolveStream(videoId, quality = 'high', options = {}) {
  const visitorData   = await getVisitorData(options);
  const hasAccountAuth = options.cookie || options.refreshToken || options.accessToken;
  const clientContext = Object.assign({}, hasAccountAuth ? WEB_REMIX_CONTEXT : IOS_CONTEXT);
  if (options.hl) clientContext.hl = options.hl;
  if (options.gl) clientContext.gl = options.gl;
  if (visitorData) clientContext.visitorData = visitorData;

  const headers = {
    'Content-Type': 'application/json',
    'User-Agent': hasAccountAuth
      ? 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
      : 'com.google.ios.youtube/20.10.01 (iPhone16,2; U; CPU iOS 18_3_2 like Mac OS X)',
  };
  if (hasAccountAuth) {
    headers.Origin = YTM_BASE;
    headers.Referer = YTM_BASE + '/';
    await addAccountAuth(headers, options);
  }

  const response = await fetch(`${YTM_BASE}/youtubei/v1/player?prettyPrint=false`, {
    method:  'POST',
    headers,
    signal: AbortSignal.timeout(PLAYER_TIMEOUT_MS),
    body: JSON.stringify({
      context:      { client: clientContext },
      videoId,
      contentCheckOk: true,
      racyCheckOk:    true,
    }),
  });

  const data = await response.json();

  if (data?.playabilityStatus?.status !== 'OK') {
    cachedVisitorData = null;
    cachedVisitorDataFetchedAt = 0;
    throw new Error('Playback blocked: ' + (data?.playabilityStatus?.reason || 'unknown'));
  }

  const sd = data.streamingData;
  if (!sd) throw new Error('No streaming data returned');

  const directFormat = pickDirectAudioFormat(sd.adaptiveFormats, quality);

  if (options.directOnly) {
    if (!directFormat) throw new Error('No direct downloadable audio found for ' + videoId);
    console.log('[YTMusic] Direct audio for', videoId, 'itag:', directFormat.itag);
    return {
      url: directFormat.url,
      format: formatFromMimeType(directFormat.mimeType),
      quality,
      contentType: directFormat.mimeType?.split(';')[0],
    };
  }

  // Strategy 1: HLS manifest — preferred, native support in Eclipse
  if (sd.hlsManifestUrl) {
    console.log('[YTMusic] HLS stream for', videoId);
    return { url: sd.hlsManifestUrl, format: 'aac', quality };
  }

  // Strategy 2: Direct mp4 audio URL
  if (directFormat) {
    console.log('[YTMusic] Direct audio for', videoId, 'itag:', directFormat.itag);
    return {
      url: directFormat.url,
      format: formatFromMimeType(directFormat.mimeType),
      quality,
      contentType: directFormat.mimeType?.split(';')[0],
    };
  }

  throw new Error('No playable audio found for ' + videoId);
}

async function resolveDownload(videoId, quality = '128', options = {}) {
  const streamQuality = quality === '320' ? 'high' : 'low';

  // Prefer URLs tied directly to the requested YouTube Music video so we
  // don't accidentally return mismatched third-party audio. For playback,
  // HLS is fine here and often more reliable than direct adaptive audio.
  if (!options.skipStream) {
    try {
      return await resolveStream(videoId, streamQuality, options);
    } catch (streamError) {
      console.warn('[YTMusic] Direct stream unavailable for', videoId, '-', streamError.message);
    }
  }

  try {
    return await resolveWithYtDlp(videoId, streamQuality, options);
  } catch (ytDlpError) {
    console.warn('[YTMusic] yt-dlp fallback unavailable for', videoId, '-', ytDlpError.message);
  }

  try {
    const response = await fetch(`${DOWNLOAD_API_BASE}${encodeURIComponent(videoId)}?s=5`, {
      signal: AbortSignal.timeout(DOWNLOAD_API_TIMEOUT_MS),
    });
    if (!response.ok) {
      throw new Error('HTTP ' + response.status);
    }

    const data = await response.json();
    if (!data.downloadUrl) {
      throw new Error('No download URL returned');
    }

    return {
      url: data.downloadUrl,
      format: 'mp3',
      quality: streamQuality,
    };
  } catch (downloadError) {
    console.warn('[YTMusic] Download API unavailable for', videoId, '-', downloadError.message);
    throw downloadError;
  }
}

async function getAlbum(albumId, options = {}) {
  const headers = {
    'Content-Type': 'application/json',
    'Origin':       YTM_BASE,
    'Referer':      YTM_BASE + '/',
    'User-Agent':   'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
  };
  await addAccountAuth(headers, options);
  const client = {
    ...WEB_REMIX_CONTEXT,
    ...(options.hl ? { hl: options.hl } : {}),
    ...(options.gl ? { gl: options.gl } : {}),
  };

  const response = await fetch(`${YTM_BASE}/youtubei/v1/browse?key=${YTM_API_KEY}`, {
    method: 'POST',
    headers,
    body: JSON.stringify({
      context:  { client },
      browseId: albumId,
    }),
  });

  const data = await response.json();

  if (data?.responseContext?.visitorData) {
    cachedVisitorData = data.responseContext.visitorData;
    cachedVisitorDataFetchedAt = Date.now();
  }

  const header =
    data?.header?.musicImmersiveHeaderRenderer ||
    data?.header?.musicDetailHeaderRenderer || {};

  const albumTitle = header?.title?.runs?.[0]?.text || '';
  let albumArtist = '';
  if (header?.subtitle?.runs) {
    for (const run of header.subtitle.runs) {
      if (run.navigationEndpoint?.browseEndpoint) {
        albumArtist = run.text;
        break;
      }
    }
  }
  const albumCover = bestThumbnail(
    header?.thumbnail?.musicThumbnailRenderer?.thumbnail?.thumbnails || []
  );

  const contents =
    data?.contents?.singleColumnBrowseResultsRenderer?.tabs?.[0]
      ?.tabRenderer?.content?.sectionListRenderer?.contents?.[0]
      ?.musicShelfRenderer?.contents || [];

  const tracks = contents
    .filter(c => c.musicResponsiveListItemRenderer?.playlistItemData?.videoId)
    .map(c => {
      const r = c.musicResponsiveListItemRenderer;
      return {
        id:         r.playlistItemData.videoId,
        title:      r.flexColumns?.[0]?.musicResponsiveListItemFlexColumnRenderer?.text?.runs?.[0]?.text || '',
        artist:     albumArtist,
        album:      albumTitle,
        duration:   parseDuration(
          r.fixedColumns?.[0]?.musicResponsiveListItemFixedColumnRenderer?.text?.runs?.[0]?.text || ''
        ),
        artworkURL: albumCover,
        albumCover,
        format:     'aac',
      };
    });

  return {
    id:         albumId,
    title:      albumTitle,
    artist:     albumArtist,
    artworkURL: albumCover,
    albumCover,
    trackCount: tracks.length,
    tracks,
  };
}

// ─── Eclipse HTTP endpoints ───────────────────────────────────────────────────

app.get(['/setup', '/ytmusic/setup'], (req, res) => {
  res.type('html').send(setupPageHtml(req));
});

app.post(['/api/setup', '/ytmusic/api/setup'], async (req, res) => {
  const wantsJson = req.is('application/json') || /\bapplication\/json\b/.test(req.get('accept') || '');
  try {
    const sessionId = await createTokenSession(req.body.refreshToken, req.body.gl, req.body.hl);
    const installUrl = `${getBaseUrl(req)}/u/${encodeURIComponent(sessionId)}/manifest.json`;
    if (wantsJson) return res.json({ url: installUrl, installUrl });
    res.type('html').send(setupPageHtml(req, installUrl));
  } catch (e) {
    console.error('[setup]', e.message);
    if (wantsJson) return res.status(400).json({ error: e.message });
    res.status(400).type('html').send(setupPageHtml(req, '', e.message));
  }
});

app.get(['/cookie', '/ytmusic/cookie'], (req, res) => {
  res.type('html').send(cookiePageHtml(req));
});

app.post(['/cookie', '/ytmusic/cookie'], (req, res) => {
  try {
    const sessionId = createCookieSession(req.body.cookie);
    const installUrl = `${getBaseUrl(req)}/u/${encodeURIComponent(sessionId)}/manifest.json`;
    res.type('html').send(cookiePageHtml(req, installUrl));
  } catch (e) {
    res.status(400).type('html').send(cookiePageHtml(req, '', e.message));
  }
});

app.use(['/u/:sessionId', '/ytmusic/u/:sessionId'], requireCookieSession);

app.get(['/u/:sessionId/manifest.json', '/ytmusic/u/:sessionId/manifest.json'], (req, res) => {
  res.json(manifestResponse(req));
});

app.get(['/u/:sessionId/search', '/ytmusic/u/:sessionId/search'], async (req, res) => {
  const query = (req.query.q || '').trim();
  if (!query) return res.json({ tracks: [] });

  try {
    const tracks = await searchYTMusicWithFallback(query, 20, getSessionOptions(req));
    res.json({ tracks: withStreamUrls(req, tracks) });
  } catch (e) {
    console.error('[search]', e.message);
    res.status(500).json({ error: e.message });
  }
});

app.get(['/u/:sessionId/stream/:id', '/ytmusic/u/:sessionId/stream/:id'], async (req, res) => {
  const videoId = req.params.id;
  const options = getSessionOptions(req);
  try {
    res.json(await resolvePlaybackForEclipse(req, videoId, options));
  } catch (e) {
    if (options.cookie || options.refreshToken || options.accessToken) {
      try {
        console.warn('[stream]', videoId, 'account-auth failed, retrying anonymous:', e.message);
        return res.json(await resolvePlaybackForEclipse(req, videoId));
      } catch (fallbackError) {
        console.error('[stream]', videoId, fallbackError.message);
        return res.status(500).json({ error: fallbackError.message });
      }
    }
    console.error('[stream]', videoId, e.message);
    res.status(500).json({ error: e.message });
  }
});

app.get(['/u/:sessionId/stream-proxy/:id', '/ytmusic/u/:sessionId/stream-proxy/:id'], async (req, res) => {
  await streamProxyAudio(req, res, getProxyVideoId(req.params.id), getSessionOptions(req));
});

app.get(['/u/:sessionId/stream-proxy-token/:token', '/ytmusic/u/:sessionId/stream-proxy-token/:token'], async (req, res) => {
  const token = getProxyVideoId(req.params.token);
  const result = getProxiedUrl(token);
  if (!result) return res.status(404).json({ error: 'Audio URL expired. Press play again.' });

  try {
    await proxyAudioResponse(req, res, result);
  } catch (e) {
    console.error('[stream-proxy-token]', e.message);
    res.status(502).json({ error: e.message });
  }
});

app.get(['/u/:sessionId/download/:id', '/ytmusic/u/:sessionId/download/:id'], async (req, res) => {
  const videoId = req.params.id;
  const quality = (req.query.quality || '128').toLowerCase();

  try {
    const result = await resolveDownload(videoId, quality, {
      ...getSessionOptions(req),
      directOnly: true,
    });
    await proxyAudioResponse(req, res, result);
  } catch (e) {
    console.error('[download]', videoId, e.message);
    res.status(500).json({ error: e.message });
  }
});

app.get(['/u/:sessionId/proxy/:token', '/ytmusic/u/:sessionId/proxy/:token'], async (req, res) => {
  const result = getProxiedUrl(req.params.token);
  if (!result) return res.status(404).json({ error: 'Audio URL expired. Press play again.' });

  try {
    await proxyAudioResponse(req, res, result);
  } catch (e) {
    console.error('[proxy]', e.message);
    res.status(502).json({ error: e.message });
  }
});

app.get(['/u/:sessionId/audio/:id', '/ytmusic/u/:sessionId/audio/:id'], (req, res) => {
  const quality = req.query.quality ? `?quality=${encodeURIComponent(req.query.quality)}` : '';
  res.redirect(302, `${getBaseUrl(req)}/u/${encodeURIComponent(req.params.sessionId)}/download/${encodeURIComponent(req.params.id)}${quality}`);
});

app.get(['/u/:sessionId/album/:id', '/ytmusic/u/:sessionId/album/:id'], async (req, res) => {
  const albumId = req.params.id;
  try {
    const album = await getAlbum(albumId, getSessionOptions(req));
    album.tracks = withStreamUrls(req, album.tracks);
    res.json(album);
  } catch (e) {
    console.error('[album]', albumId, e.message);
    res.status(500).json({ error: e.message });
  }
});

// GET /manifest.json
app.get(['/manifest.json', '/ytmusic/manifest.json'], (req, res) => {
  res.json(manifestResponse(req));
});

// GET /search?q={query}
app.get(['/search', '/ytmusic/search'], async (req, res) => {
  const query = (req.query.q || '').trim();
  if (!query) return res.json({ tracks: [] });

  try {
    const tracks = await searchYTMusicWithFallback(query, 20);
    res.json({ tracks: withStreamUrls(req, tracks) });
  } catch (e) {
    console.error('[search]', e.message);
    res.status(500).json({ error: e.message });
  }
});

// GET /stream/:videoId
// Eclipse calls this at play time AND when saving for offline.
// Returns { url, format, quality } — Eclipse downloads the audio file
// and caches it locally; offline playback needs no addon server.
app.get(['/stream/:id', '/ytmusic/stream/:id'], async (req, res) => {
  const videoId = req.params.id;
  try {
    res.json(await resolvePlaybackForEclipse(req, videoId));
  } catch (e) {
    console.error('[stream]', videoId, e.message);
    res.status(500).json({ error: e.message });
  }
});

app.get(['/stream-proxy/:id', '/ytmusic/stream-proxy/:id'], async (req, res) => {
  await streamProxyAudio(req, res, getProxyVideoId(req.params.id));
});

app.get(['/stream-proxy-token/:token', '/ytmusic/stream-proxy-token/:token'], async (req, res) => {
  const token = getProxyVideoId(req.params.token);
  const result = getProxiedUrl(token);
  if (!result) return res.status(404).json({ error: 'Audio URL expired. Press play again.' });

  try {
    await proxyAudioResponse(req, res, result);
  } catch (e) {
    console.error('[stream-proxy-token]', e.message);
    res.status(502).json({ error: e.message });
  }
});

// GET /download/:videoId
// Track-level streamURL targets this endpoint so Eclipse can save tracks
// offline. The updated 8spine module uses y2jar for downloadable files, while
// /stream/:id stays on YouTube Music HLS for playback.
app.get(['/download/:id', '/ytmusic/download/:id'], async (req, res) => {
  const videoId = req.params.id;
  const quality = (req.query.quality || '128').toLowerCase();

  try {
    const result = await resolveDownload(videoId, quality, { directOnly: true });
    await proxyAudioResponse(req, res, result);
  } catch (e) {
    console.error('[download]', videoId, e.message);
    res.status(500).json({ error: e.message });
  }
});

app.get(['/proxy/:token', '/ytmusic/proxy/:token'], async (req, res) => {
  const result = getProxiedUrl(req.params.token);
  if (!result) return res.status(404).json({ error: 'Audio URL expired. Press play again.' });

  try {
    await proxyAudioResponse(req, res, result);
  } catch (e) {
    console.error('[proxy]', e.message);
    res.status(502).json({ error: e.message });
  }
});

// Backward-compatible alias for tracks returned by earlier local builds.
app.get(['/audio/:id', '/ytmusic/audio/:id'], (req, res) => {
  const quality = req.query.quality ? `?quality=${encodeURIComponent(req.query.quality)}` : '';
  res.redirect(302, `${getBaseUrl(req)}/download/${encodeURIComponent(req.params.id)}${quality}`);
});

// GET /album/:browseId
// Eclipse calls this when a user taps an album in search results.
// Returns full track listing; Eclipse can bulk-save for offline.
app.get(['/album/:id', '/ytmusic/album/:id'], async (req, res) => {
  const albumId = req.params.id;
  try {
    const album = await getAlbum(albumId);
    album.tracks = withStreamUrls(req, album.tracks);
    res.json(album);
  } catch (e) {
    console.error('[album]', albumId, e.message);
    res.status(500).json({ error: e.message });
  }
});

// Root info
app.get(['/', '/ytmusic'], (req, res) => {
  res.json({
    addon:   'Eclipse YouTube Music Addon',
    install: `Open Eclipse → Settings → Connections → Add Addon → paste: ${getBaseUrl(req)}/manifest.json`,
    docs:    'https://eclipsemusic.app/docs',
  });
});

const PORT = process.env.PORT || 3000;
app.listen(PORT, () => {
  console.log(`\n🎵 Eclipse YouTube Music Addon running on http://localhost:${PORT}`);
  console.log(`   Install in Eclipse: http://localhost:${PORT}/manifest.json\n`);
});
