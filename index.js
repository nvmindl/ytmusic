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
const os = require('os');
const path = require('path');
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
const COOKIE_SESSION_TTL_MS = 12 * 60 * 60 * 1000;
const PLAYER_TIMEOUT_MS = 5000;
const DOWNLOAD_API_TIMEOUT_MS = 6000;
const YT_DLP_UNAVAILABLE_TTL_MS = 5 * 60 * 1000;
let cachedVisitorData = null;
let cachedVisitorDataFetchedAt = 0;
const extractedUrlCache = new Map();
const cookieSessions = new Map();
let ytDlpUnavailableUntil = 0;

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
  const baseUrl = getBaseUrl(req);
  const sessionBasePath = getSessionBasePath(req);
  return tracks.map(track => ({
    ...track,
    streamURL: `${baseUrl}${sessionBasePath}/download/${encodeURIComponent(track.id)}`,
  }));
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
  return id;
}

function getCookieSession(id) {
  if (!id) return null;
  const session = cookieSessions.get(id);
  if (!session) return null;
  if ((Date.now() - session.createdAt) >= COOKIE_SESSION_TTL_MS) {
    cookieSessions.delete(id);
    return null;
  }
  session.lastUsedAt = Date.now();
  return session;
}

function getSessionOptions(req) {
  return {
    cookie: req.cookieSession?.cookie || null,
  };
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
  const cookiePageUrl = `${baseUrl}/cookie`;
  const description = req.cookieSessionId
    ? 'Stream YouTube Music with your private cookie-backed session. This session expires automatically.'
    : `Stream YouTube Music HLS with refreshed visitor sessions. If playback is blocked, create a cookie-backed install URL at ${cookiePageUrl}.`;

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
  if (options.cookie) headers.Cookie = options.cookie;

  const response = await fetch(`${YTM_BASE}/youtubei/v1/search?key=${YTM_API_KEY}`, {
    method: 'POST',
    headers,
    body: JSON.stringify({
      context: { client: WEB_REMIX_CONTEXT },
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
  const cacheKey = `${videoId}:${quality}:${options.cookie ? 'cookie' : 'anon'}`;
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
  const clientContext = Object.assign({}, options.cookie ? WEB_REMIX_CONTEXT : IOS_CONTEXT);
  if (visitorData) clientContext.visitorData = visitorData;

  const headers = {
    'Content-Type': 'application/json',
    'User-Agent': options.cookie
      ? 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
      : 'com.google.ios.youtube/20.10.01 (iPhone16,2; U; CPU iOS 18_3_2 like Mac OS X)',
  };
  if (options.cookie) {
    headers.Cookie = options.cookie;
    headers.Origin = YTM_BASE;
    headers.Referer = YTM_BASE + '/';
    headers['X-Origin'] = YTM_BASE;
    headers['X-Goog-AuthUser'] = '0';
    const authHeader = getSapisidAuthHeader(options.cookie, YTM_BASE);
    if (authHeader) headers.Authorization = authHeader;
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
  if (options.cookie) headers.Cookie = options.cookie;

  const response = await fetch(`${YTM_BASE}/youtubei/v1/browse?key=${YTM_API_KEY}`, {
    method: 'POST',
    headers,
    body: JSON.stringify({
      context:  { client: WEB_REMIX_CONTEXT },
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
    const tracks = await searchYTMusic(query, 20);
    res.json({ tracks: withStreamUrls(req, tracks) });
  } catch (e) {
    console.error('[search]', e.message);
    res.status(500).json({ error: e.message });
  }
});

app.get(['/u/:sessionId/stream/:id', '/ytmusic/u/:sessionId/stream/:id'], async (req, res) => {
  const videoId = req.params.id;
  const quality = (req.query.quality || 'high').toLowerCase();
  const sessionOptions = getSessionOptions(req);

  try {
    const result = await resolveStream(videoId, quality, sessionOptions);
    res.json(result);
  } catch (e) {
    try {
      const result = await resolveDownload(videoId, quality === 'high' ? '320' : '128', {
        ...sessionOptions,
        skipStream: true,
      });
      res.json(result);
    } catch (fallbackError) {
      console.error('[stream]', videoId, e.message);
      console.error('[stream-download-fallback]', videoId, fallbackError.message);
      res.status(500).json({ error: e.message });
    }
  }
});

app.get(['/u/:sessionId/download/:id', '/ytmusic/u/:sessionId/download/:id'], async (req, res) => {
  const videoId = req.params.id;
  const quality = (req.query.quality || '128').toLowerCase();

  try {
    const result = await resolveDownload(videoId, quality, getSessionOptions(req));
    res.redirect(302, result.url);
  } catch (e) {
    console.error('[download]', videoId, e.message);
    res.status(500).json({ error: e.message });
  }
});

app.get(['/u/:sessionId/audio/:id', '/ytmusic/u/:sessionId/audio/:id'], (req, res) => {
  const quality = req.query.quality ? `?quality=${encodeURIComponent(req.query.quality)}` : '';
  res.redirect(302, `${getBaseUrl(req)}/u/${encodeURIComponent(req.params.sessionId)}/download/${encodeURIComponent(req.params.id)}${quality}`);
});

app.get(['/u/:sessionId/album/:id', '/ytmusic/u/:sessionId/album/:id'], async (req, res) => {
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

// GET /manifest.json
app.get(['/manifest.json', '/ytmusic/manifest.json'], (req, res) => {
  res.json(manifestResponse(req));
});

// GET /search?q={query}
app.get(['/search', '/ytmusic/search'], async (req, res) => {
  const query = (req.query.q || '').trim();
  if (!query) return res.json({ tracks: [] });

  try {
    const tracks = await searchYTMusic(query, 20);
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
  // Quality from query param: ?quality=low|high|lossless (default: high)
  const quality = (req.query.quality || 'high').toLowerCase();

  try {
    const result = await resolveStream(videoId, quality);
    res.json(result);
  } catch (e) {
    try {
      const result = await resolveDownload(videoId, quality === 'high' ? '320' : '128', {
        skipStream: true,
      });
      res.json(result);
    } catch (fallbackError) {
      console.error('[stream]', videoId, e.message);
      console.error('[stream-download-fallback]', videoId, fallbackError.message);
      res.status(500).json({ error: e.message });
    }
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
    const result = await resolveDownload(videoId, quality);
    res.redirect(302, result.url);
  } catch (e) {
    console.error('[download]', videoId, e.message);
    res.status(500).json({ error: e.message });
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
