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
const ISSUE_TOKEN_CLIENT_ID = process.env.GOOGLE_ISSUE_TOKEN_CLIENT_ID || '755973059757-iigsfdoqt2c4qm209soqp2dlrh33almr.apps.googleusercontent.com';
const ISSUE_TOKEN_APP_ID = 'com.google.ios.youtubemusic';
const YOUTUBE_SCOPE = 'https://www.googleapis.com/auth/youtube';
const ISSUE_TOKEN_SCOPE = YOUTUBE_SCOPE;

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

const IOS_MUSIC_CONTEXT = {
  clientName:    26,
  clientVersion: '9.18.2',
  deviceMake:    'Apple',
  deviceModel:   'iPhone17,3',
  osName:        'iPhone',
  osVersion:     '26.1',
  hl: 'en',
  gl: 'SA',
};

// ─── In-memory visitorData cache ──────────────────────────────────────────────
// Captured from every WEB_REMIX search response and forwarded to the IOS
// player to pass YouTube's bot detection — same technique as the 8spine module.
const VISITOR_DATA_TTL_MS = 20 * 60 * 1000;
const URL_CACHE_TTL_MS = 10 * 60 * 1000;
const PROXY_URL_TTL_MS = 20 * 60 * 1000;
const COOKIE_SESSION_TTL_MS = 12 * 60 * 60 * 1000;
const TOKEN_SESSION_TTL_MS = 30 * 24 * 60 * 60 * 1000;
const PLAYER_TIMEOUT_MS = 8000;
const DOWNLOAD_API_TIMEOUT_MS = 5000;
const YT_DLP_UNAVAILABLE_TTL_MS = 5 * 60 * 1000;
const STREAM_FAILURE_TTL_MS = 30 * 1000;
let cachedVisitorData = null;
let cachedVisitorDataFetchedAt = 0;
const extractedUrlCache = new Map();
const proxiedUrlCache = new Map();
const streamResolutionCache = new Map();
const streamResolutionInflight = new Map();
const streamResolutionFailures = new Map();
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

function redactSecrets(text) {
  return String(text || '')
    .replace(/Bearer\s+1\/\/[A-Za-z0-9._-]+/g, 'Bearer [redacted]')
    .replace(/Bearer\s+ya29\.[A-Za-z0-9._-]+/g, 'Bearer [redacted]')
    .replace(/1\/\/[A-Za-z0-9._-]{16,}/g, '1//[redacted]')
    .replace(/ya29\.[A-Za-z0-9._-]{16,}/g, 'ya29.[redacted]');
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
  const language = String(hl || 'en-US').includes('-') ? String(hl || 'en-US') : `${String(hl || 'en')}-US`;
  const body = new URLSearchParams({
    app_id: ISSUE_TOKEN_APP_ID,
    client_id: ISSUE_TOKEN_CLIENT_ID,
    device_id: crypto.randomUUID().toUpperCase(),
    hl: language,
    lib_ver: '3.4',
    response_type: 'token',
    scope: ISSUE_TOKEN_SCOPE,
  });

  const response = await fetch('https://oauthaccountmanager.googleapis.com/v1/issuetoken', {
    method: 'POST',
    headers: {
      'Accept': '*/*',
      'Accept-Encoding': 'gzip, deflate, br',
      'Accept-Language': 'en-US,en;q=0.9',
      'Authorization': `Bearer ${refreshToken}`,
      'Content-Type': 'application/x-www-form-urlencoded',
      'X-OAuth-Client-ID': ISSUE_TOKEN_CLIENT_ID,
      'User-Agent': 'com.google.ios.youtubemusic/9.18.2 iSL/3.4 iPhone/26.1 hw/iPhone17_3 (gzip)',
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
    scope: data.scope || data.grantedScopes || ISSUE_TOKEN_SCOPE,
  };
}

async function refreshAccessToken(session, force = false) {
  if (!session?.refreshToken) return null;
  const hasExpectedIssueTokenScope = session.tokenSource !== 'issuetoken' || session.accessTokenScope === ISSUE_TOKEN_SCOPE;
  if (!force && hasExpectedIssueTokenScope && session.accessToken && session.accessTokenExpiresAt > (Date.now() + 60_000)) {
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
  session.accessTokenScope = data.scope || ISSUE_TOKEN_SCOPE;
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
    tokenSource: req.cookieSession?.tokenSource || null,
    gl: req.cookieSession?.gl || null,
    hl: req.cookieSession?.hl || null,
  };
}

async function addAccountAuth(headers, options = {}) {
  if (options.tokenSession?.refreshToken) {
    const accessToken = await refreshAccessToken(
      options.tokenSession,
      options.tokenSession.tokenSource === 'raw-bearer'
    );
    if (accessToken) {
      headers.Authorization = `Bearer ${accessToken}`;
      headers['X-Goog-AuthUser'] = '0';
    }
  }
  if (!headers.Authorization && options.accessToken) {
    headers.Authorization = `Bearer ${options.accessToken}`;
    headers['X-Goog-AuthUser'] = '0';
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
    <p>Paste either the YouTube Music <code>1//</code> mobile token or a full browser Cookie header to generate a private Eclipse install URL.</p>
    <form method="post" action="cookie">
      <label for="cookie">Token or Cookie header</label>
      <textarea id="cookie" name="cookie" autocomplete="off" spellcheck="false" placeholder="1//0... or VISITOR_INFO1_LIVE=...; __Secure-1PSID=..."></textarea>
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

function normalizeForMatch(value = '') {
  return String(value)
    .toLowerCase()
    .replace(/\([^)]*\)|\[[^\]]*\]/g, ' ')
    .replace(/&/g, ' and ')
    .replace(/[^a-z0-9]+/g, ' ')
    .trim();
}

function uniqueWords(value = '') {
  return [...new Set(normalizeForMatch(value).split(/\s+/).filter(Boolean))];
}

function rankSearchTracks(query, tracks, limit) {
  const queryNorm = normalizeForMatch(query);
  const queryWords = uniqueWords(query);
  const queryHasVariant = /\b(instrumental|karaoke|cover|remix|live|sped|slowed|nightcore|acoustic|version)\b/i.test(query);
  const seenIds = new Set();
  const seenSongs = new Set();

  return tracks
    .filter(track => {
      if (!track?.id || seenIds.has(track.id)) return false;
      seenIds.add(track.id);

      const songKey = `${normalizeForMatch(track.title)}::${normalizeForMatch(track.artist)}`;
      if (songKey !== '::' && seenSongs.has(songKey)) return false;
      seenSongs.add(songKey);
      return true;
    })
    .map((track, index) => {
      const titleNorm = normalizeForMatch(track.title);
      const artistNorm = normalizeForMatch(track.artist);
      const albumNorm = normalizeForMatch(track.album);
      const haystack = `${titleNorm} ${artistNorm} ${albumNorm}`.trim();
      let score = 0;

      if (queryNorm && haystack.includes(queryNorm)) score += 80;
      if (queryNorm && `${titleNorm} ${artistNorm}`.includes(queryNorm)) score += 120;
      if (titleNorm && queryNorm.includes(titleNorm)) score += 60;
      if (artistNorm && queryNorm.includes(artistNorm)) score += 80;

      const matchedWords = queryWords.filter(word => haystack.includes(word)).length;
      score += matchedWords * 12;
      if (queryWords.length && matchedWords === queryWords.length) score += 40;

      const variantText = `${track.title} ${track.artist} ${track.album}`;
      if (!queryHasVariant && /\b(instrumental|karaoke|cover|remix|live|sped|slowed|nightcore|acoustic)\b/i.test(variantText)) {
        score -= 90;
      }
      if (/topic$/i.test(track.artist || '')) score += 8;
      if (track.duration > 0) score += 5;

      return { track, score, index };
    })
    .sort((a, b) => (b.score - a.score) || (a.index - b.index))
    .slice(0, limit)
    .map(entry => entry.track);
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
      if (tracks.length >= Math.max(limit * 2, 40)) break;
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

  return rankSearchTracks(query, tracks, limit);
}

async function searchYTMusicWithFallback(query, limit = 20, options = {}) {
  if (options.tokenSource === 'raw-bearer') {
    return searchYTMusic(query, limit);
  }

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

  const bitrate = format => Number(format.bitrate || format.averageBitrate || 0);
  const isMp4 = format => format.mimeType?.startsWith('audio/mp4') ? 1 : 0;

  if (quality !== 'low') {
    const itag140 = directFormats.find(format => Number(format.itag) === 140 && isMp4(format));
    if (itag140) return itag140;
  }

  directFormats.sort((a, b) => {
    const aIsMp4 = isMp4(a);
    const bIsMp4 = isMp4(b);
    if (aIsMp4 !== bIsMp4) return bIsMp4 - aIsMp4;

    if (quality === 'low') {
      return bitrate(a) - bitrate(b);
    }

    const target = 128000;
    return Math.abs(bitrate(a) - target) - Math.abs(bitrate(b) - target);
  });
  return quality === 'low'
    ? directFormats[0]
    : directFormats[0];
}

function formatFromMimeType(mimeType = '') {
  if (mimeType.includes('audio/mp4')) return 'm4a';
  if (mimeType.includes('audio/webm')) return 'ogg';
  if (mimeType.includes('audio/ogg')) return 'ogg';
  return 'aac';
}

function durationFromPlayerData(data, format = {}) {
  const approxMs = Number(format.approxDurationMs || 0);
  if (approxMs > 0) return Math.round(approxMs / 1000);
  const detailsSeconds = Number(data?.videoDetails?.lengthSeconds || 0);
  if (detailsSeconds > 0) return Math.round(detailsSeconds);
  return 0;
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

function getAuthCacheKey(options = {}) {
  const authMaterial =
    options.cookie ||
    options.accessToken ||
    options.refreshToken ||
    options.tokenSource ||
    'anon';
  return crypto.createHash('sha1').update(String(authMaterial)).digest('hex').slice(0, 16);
}

function getCachedStreamResolution(cacheKey) {
  const entry = streamResolutionCache.get(cacheKey);
  if (!entry) return null;
  if ((Date.now() - entry.createdAt) >= URL_CACHE_TTL_MS) {
    streamResolutionCache.delete(cacheKey);
    return null;
  }
  return entry.value;
}

function setCachedStreamResolution(cacheKey, value) {
  streamResolutionCache.set(cacheKey, {
    createdAt: Date.now(),
    value,
  });
  streamResolutionFailures.delete(cacheKey);
}

function getCachedStreamFailure(cacheKey) {
  const entry = streamResolutionFailures.get(cacheKey);
  if (!entry) return null;
  if ((Date.now() - entry.createdAt) >= STREAM_FAILURE_TTL_MS) {
    streamResolutionFailures.delete(cacheKey);
    return null;
  }
  return entry.error;
}

function setCachedStreamFailure(cacheKey, error) {
  streamResolutionFailures.set(cacheKey, {
    createdAt: Date.now(),
    error,
  });
}

async function validateAudioResult(result) {
  const response = await fetch(result.url, {
    headers: { Range: 'bytes=0-0' },
    signal: AbortSignal.timeout(8000),
  });
  const contentType = response.headers.get('content-type') || result.contentType || '';
  const contentLength = Number(response.headers.get('content-length') || 0);
  const contentRange = response.headers.get('content-range') || '';
  const rangeLength = Number(contentRange.match(/\/(\d+)$/)?.[1] || 0);
  if (response.body?.cancel) response.body.cancel().catch(() => {});
  if (!response.ok && response.status !== 206) {
    throw new Error(`Candidate audio URL failed: HTTP ${response.status}`);
  }
  if (!/audio|octet-stream|video\/mp4/i.test(contentType)) {
    throw new Error(`Candidate audio URL is non-audio (${contentType || 'unknown'})`);
  }
  if (!contentRange && contentLength > 0 && contentLength < 32) {
    throw new Error(`Candidate audio URL is too small (${contentLength} bytes)`);
  }
  return {
    ...result,
    url: response.url || result.url,
    contentType: contentType || result.contentType,
    contentLength: rangeLength || result.contentLength || contentLength || undefined,
  };
}

async function resolveProxyAudio(videoId, options = {}) {
  const cacheKey = `${videoId}:${getAuthCacheKey(options)}`;
  const cached = getCachedStreamResolution(cacheKey);
  if (cached) return cached;
  const cachedFailure = getCachedStreamFailure(cacheKey);
  if (cachedFailure) throw cachedFailure;
  if (streamResolutionInflight.has(cacheKey)) {
    return streamResolutionInflight.get(cacheKey);
  }

  const promise = (async () => {
    const attempts = [
      resolveStream(videoId, 'high', {
        ...options,
        directOnly: true,
      }).then(validateAudioResult),
      resolveDownloadApi(videoId, 'high').then(validateAudioResult),
    ];

    if (!options.accessToken && options.tokenSource !== 'raw-bearer') {
      attempts.push(resolveWithYtDlp(videoId, 'high', options).then(validateAudioResult));
    }

    try {
      const result = await Promise.any(attempts);
      setCachedStreamResolution(cacheKey, result);
      return result;
    } catch (aggregateError) {
      const reasons = (aggregateError.errors || [aggregateError])
        .map(e => redactSecrets(e.message))
        .join(' | ');
      const error = new Error(reasons || 'No playable audio found');
      setCachedStreamFailure(cacheKey, error);
      console.error('[stream-proxy]', videoId, reasons);
      throw error;
    }
  })().finally(() => {
    streamResolutionInflight.delete(cacheKey);
  });

  streamResolutionInflight.set(cacheKey, promise);
  return promise;
}

function warmProxyAudio(videoId, options = {}) {
  resolveProxyAudio(videoId, options).catch(e => {
    console.warn('[stream-warm]', videoId, e.message);
  });
}

function warmDirectAudio(videoId, options = {}) {
  if (!videoId || !(options.cookie || options.refreshToken || options.accessToken)) return;
  const cacheKey = `${videoId}:${getAuthCacheKey(options)}`;
  if (getCachedStreamResolution(cacheKey) || streamResolutionInflight.has(cacheKey)) return;

  const promise = resolveStream(videoId, 'high', {
    ...options,
    directOnly: true,
  })
    .then(validateAudioResult)
    .then(result => {
      setCachedStreamResolution(cacheKey, result);
      return result;
    })
    .catch(e => {
      console.warn('[stream-prewarm]', videoId, redactSecrets(e.message));
    })
    .finally(() => {
      streamResolutionInflight.delete(cacheKey);
    });

  streamResolutionInflight.set(cacheKey, promise);
}

function warmDirectAudioForTracks(tracks, options = {}, limit = 10) {
  if (!Array.isArray(tracks) || !(options.cookie || options.refreshToken || options.accessToken)) return;
  for (const [index, track] of tracks.slice(0, limit).entries()) {
    const delay = index < 3 ? 0 : (index - 2) * 600;
    setTimeout(() => {
      warmDirectAudio(track.id, options);
    }, delay);
  }
}

async function prepareDirectAudioForTracks(tracks, options = {}, limit = 3) {
  if (!Array.isArray(tracks) || !(options.cookie || options.refreshToken || options.accessToken)) return;
  const selected = tracks.slice(0, limit).filter(track => track?.id);
  await Promise.allSettled(selected.map(track => {
    const cacheKey = `${track.id}:${getAuthCacheKey(options)}`;
    if (getCachedStreamResolution(cacheKey)) return Promise.resolve();
    if (streamResolutionInflight.has(cacheKey)) return streamResolutionInflight.get(cacheKey);

    const promise = resolveStream(track.id, 'high', {
      ...options,
      directOnly: true,
    })
      .then(validateAudioResult)
      .then(result => {
        setCachedStreamResolution(cacheKey, result);
        return result;
      })
      .catch(e => {
        console.warn('[stream-prepare]', track.id, redactSecrets(e.message));
      })
      .finally(() => {
        streamResolutionInflight.delete(cacheKey);
      });

    streamResolutionInflight.set(cacheKey, promise);
    return promise;
  }));
}

function applyPreparedAudioMetadata(tracks, options = {}) {
  if (!Array.isArray(tracks) || !(options.cookie || options.refreshToken || options.accessToken)) return tracks;
  return tracks.map(track => {
    const prepared = getCachedStreamResolution(`${track.id}:${getAuthCacheKey(options)}`);
    if (!prepared) return track;

    const duration = track.duration || prepared.duration || 0;
    return {
      ...track,
      duration,
      durationMs: duration ? duration * 1000 : (prepared.durationMs || 0),
      contentType: prepared.contentType || track.contentType,
      contentLength: prepared.contentLength || track.contentLength,
      format: prepared.format || track.format,
    };
  });
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
  const sessionBasePath = getSessionBasePath(req);
  if (options.cookie || options.refreshToken || options.accessToken) {
    try {
      const cacheKey = `${videoId}:${getAuthCacheKey(options)}`;
      const direct = getCachedStreamResolution(cacheKey) || await resolveStream(videoId, 'high', {
        ...options,
        directOnly: true,
      }).then(validateAudioResult);
      setCachedStreamResolution(cacheKey, direct);
      if (process.env.RETURN_DIRECT_AUDIO_URLS === '1' || req.query.direct === '1') {
        console.log('[stream]', videoId, 'returning direct audio URL');
        return {
          ...direct,
          format: direct.format || 'm4a',
          contentType: direct.contentType || 'audio/mp4',
          contentLength: direct.contentLength,
          quality: '128kbps',
          duration: direct.duration || 0,
          durationMs: direct.durationMs || ((direct.duration || 0) * 1000),
        };
      }
      console.log('[stream]', videoId, 'returning addon URL for direct audio');
      return {
        ...proxiedPlaybackResult(req, direct),
        format: direct.format || 'm4a',
        contentType: direct.contentType || 'audio/mp4',
        contentLength: direct.contentLength,
        quality: '128kbps',
        duration: direct.duration || 0,
        durationMs: direct.durationMs || ((direct.duration || 0) * 1000),
      };
    } catch (e) {
      console.warn('[stream]', videoId, 'direct user-IP audio unavailable:', redactSecrets(e.message));
    }
  }

  warmProxyAudio(videoId, options);
  return {
    url: `${getBaseUrl(req)}${sessionBasePath}/stream-proxy/${encodeURIComponent(videoId)}.m4a`,
    format: 'm4a',
    quality: '128kbps',
    duration: 0,
    durationMs: 0,
  };
}

async function proxyAudioResponse(req, res, result) {
  const upstreamHeaders = {};
  if (req.headers.range) {
    upstreamHeaders.Range = req.headers.range;
  }

  if (req.method === 'HEAD') {
    res.setHeader('Content-Type', result.contentType || 'audio/mp4');
    res.setHeader('Accept-Ranges', 'bytes');
    if (result.contentLength) res.setHeader('Content-Length', String(result.contentLength));
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.end();
    return;
  }

  const upstream = await fetch(result.url, { headers: upstreamHeaders });
  const contentType = upstream.headers.get('content-type') || result.contentType || '';
  if (!upstream.ok && upstream.status !== 206) {
    res.status(upstream.status).send(await upstream.text().catch(() => 'Upstream audio failed'));
    return;
  }
  if (!/audio|octet-stream|video\/mp4/i.test(contentType)) {
    const body = await upstream.text().catch(() => '');
    throw new Error(`Upstream returned non-audio content (${contentType || 'unknown'}): ${body.slice(0, 120)}`);
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
  const audioStream = Readable.fromWeb(upstream.body);
  audioStream.on('error', error => {
    console.warn('[proxy-audio]', 'upstream stream error:', error.message);
    if (!res.headersSent) {
      res.status(502).end('Upstream audio failed');
    } else {
      res.destroy(error);
    }
  });
  res.on('close', () => {
    audioStream.destroy();
  });
  audioStream.pipe(res);
}

async function streamProxyAudio(req, res, videoId, options = {}) {
  try {
    const result = await resolveProxyAudio(videoId, options);
    await proxyAudioResponse(req, res, result);
  } catch (e) {
    res.status(500).json({ error: e.message });
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
  if (options.accessToken || options.tokenSource === 'raw-bearer') {
    throw new Error('yt-dlp skipped for bearer token sessions');
  }

  const cacheKey = `${videoId}:${quality}:${options.cookie ? 'cookie' : options.accessToken ? 'token' : 'anon'}`;
  const cached = getCachedExtractedUrl(cacheKey);
  if (cached) return cached;
  if (options.tokenSession?.refreshToken && options.tokenSession.tokenSource === 'raw-bearer') {
    await refreshAccessToken(options.tokenSession, true);
    options.accessToken = options.tokenSession.accessToken;
    options.tokenSource = options.tokenSession.tokenSource;
  }
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
            ...(cookieTemp ? ['--cookies', cookieTemp.file] : []),
            `https://music.youtube.com/watch?v=${videoId}`,
          ],
          { timeout: options.cookie ? 15000 : 5000, maxBuffer: 1024 * 1024 }
        );
        stdout = result.stdout;
        break;
      } catch (e) {
        lastError = e;
        const message = redactSecrets((e.stderr || e.message || '').trim());
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
    const message = redactSecrets((lastError.stderr || lastError.message).trim());
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
  const isTokenAuth = options.refreshToken || options.accessToken;
  const clientContext = Object.assign({}, isTokenAuth ? IOS_MUSIC_CONTEXT : hasAccountAuth ? WEB_REMIX_CONTEXT : IOS_CONTEXT);
  if (options.hl) clientContext.hl = options.hl;
  if (options.gl) clientContext.gl = options.gl;
  if (visitorData) clientContext.visitorData = visitorData;

  const headers = {
    'Content-Type': 'application/json',
    'User-Agent': isTokenAuth
      ? 'com.google.ios.youtubemusic/9.18.2 (iPhone17,3; U; CPU iOS 26_1 like Mac OS X; en_US)'
      : hasAccountAuth
      ? 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
      : 'com.google.ios.youtube/20.10.01 (iPhone16,2; U; CPU iOS 18_3_2 like Mac OS X)',
  };
  if (isTokenAuth) {
    headers['X-Youtube-Client-Name'] = '26';
    headers['X-Youtube-Client-Version'] = IOS_MUSIC_CONTEXT.clientVersion;
    headers['X-GOOG-API-FORMAT-VERSION'] = '2';
    if (visitorData) headers['X-Goog-Visitor-Id'] = visitorData;
  }
  if (hasAccountAuth && !isTokenAuth) {
    headers.Origin = YTM_BASE;
    headers.Referer = YTM_BASE + '/';
  }
  if (hasAccountAuth) {
    await addAccountAuth(headers, options);
  }

  const playerBase = isTokenAuth ? 'https://youtubei.googleapis.com' : YTM_BASE;
  const response = await fetch(`${playerBase}/youtubei/v1/player?prettyPrint=false`, {
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
    const duration = durationFromPlayerData(data, directFormat);
    return {
      url: directFormat.url,
      format: formatFromMimeType(directFormat.mimeType),
      quality,
      contentType: directFormat.mimeType?.split(';')[0],
      contentLength: Number(directFormat.contentLength || 0) || undefined,
      duration,
      durationMs: duration * 1000,
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
    const duration = durationFromPlayerData(data, directFormat);
    return {
      url: directFormat.url,
      format: formatFromMimeType(directFormat.mimeType),
      quality,
      contentType: directFormat.mimeType?.split(';')[0],
      contentLength: Number(directFormat.contentLength || 0) || undefined,
      duration,
      durationMs: duration * 1000,
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

  return resolveDownloadApi(videoId, streamQuality);
}

async function resolveDownloadApi(videoId, streamQuality = 'high') {
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
      contentType: 'audio/mpeg',
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

app.post(['/cookie', '/ytmusic/cookie'], async (req, res) => {
  try {
    const pasted = String(req.body.cookie || '').trim();
    const isToken = /^(?:authorization:\s*)?(?:bearer\s*)?1\/\//i.test(pasted) || /^(?:bearer\s*)?ya29\./i.test(pasted);
    if (isToken) {
      const sessionId = await createTokenSession(pasted, req.body.gl || 'SA', req.body.hl || 'en');
      const installUrl = `${getBaseUrl(req)}/u/${encodeURIComponent(sessionId)}/manifest.json`;
      return res.type('html').send(cookiePageHtml(req, installUrl));
    }
    const sessionId = createCookieSession(pasted);
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
    const options = getSessionOptions(req);
    let tracks = await searchYTMusicWithFallback(query, 20, options);
    await prepareDirectAudioForTracks(tracks, options);
    tracks = applyPreparedAudioMetadata(tracks, options);
    warmDirectAudioForTracks(tracks, options);
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
    console.log('[stream-proxy-token]', req.params.sessionId, 'range:', req.headers.range || 'none');
    if (process.env.REDIRECT_AUDIO_URLS === '1' || req.query.redirect === '1') {
      return res.redirect(302, result.url);
    }
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
    const options = getSessionOptions(req);
    const album = await getAlbum(albumId, options);
    await prepareDirectAudioForTracks(album.tracks, options);
    album.tracks = applyPreparedAudioMetadata(album.tracks, options);
    warmDirectAudioForTracks(album.tracks, options);
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
    console.log('[stream-proxy-token]', 'public', 'range:', req.headers.range || 'none');
    if (process.env.REDIRECT_AUDIO_URLS === '1' || req.query.redirect === '1') {
      return res.redirect(302, result.url);
    }
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
