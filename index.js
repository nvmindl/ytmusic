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
const { promisify } = require('util');

const app = express();
app.use(cors());
app.use(express.json());
const execFileAsync = promisify(execFile);

// ─── Constants (identical to the 8spine module) ───────────────────────────────

const YTM_BASE    = 'https://music.youtube.com';
const YTM_API_KEY = 'AIzaSyC9XL3ZjWddXya6X74dJoCTL-WEYFDNX30';
const DOWNLOAD_API_BASE = 'https://capi.y2jar.cc/scr/';

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
let cachedVisitorData = null;
let cachedVisitorDataFetchedAt = 0;
const extractedUrlCache = new Map();

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
  return `${proto}://${host}`;
}

function withStreamUrls(req, tracks) {
  const baseUrl = getBaseUrl(req);
  return tracks.map(track => ({
    ...track,
    streamURL: `${baseUrl}/download/${encodeURIComponent(track.id)}`,
  }));
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

async function searchYTMusic(query, limit = 20) {
  const headers = {
    'Content-Type': 'application/json',
    'Origin':       YTM_BASE,
    'Referer':      YTM_BASE + '/',
    'User-Agent':   'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
  };

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

async function getVisitorData() {
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

async function resolveWithYtDlp(videoId, quality = 'high') {
  const cacheKey = `${videoId}:${quality}`;
  const cached = getCachedExtractedUrl(cacheKey);
  if (cached) return cached;

  const formatSelector = quality === 'low'
    ? 'bestaudio[abr<=128][ext=m4a]/bestaudio[abr<=128]/bestaudio[ext=m4a]/bestaudio'
    : 'bestaudio[ext=m4a]/bestaudio';

  const { stdout } = await execFileAsync(
    'python3',
    [
      '-m',
      'yt_dlp',
      '--no-playlist',
      '--get-url',
      '--format',
      formatSelector,
      `https://music.youtube.com/watch?v=${videoId}`,
    ],
    { timeout: 20000, maxBuffer: 1024 * 1024 }
  );

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
  const visitorData   = await getVisitorData();
  const clientContext = Object.assign({}, IOS_CONTEXT);
  if (visitorData) clientContext.visitorData = visitorData;

  const response = await fetch(`${YTM_BASE}/youtubei/v1/player?prettyPrint=false`, {
    method:  'POST',
    headers: {
      'Content-Type': 'application/json',
      'User-Agent':   'com.google.ios.youtube/20.10.01 (iPhone16,2; U; CPU iOS 18_3_2 like Mac OS X)',
    },
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

async function resolveDownload(videoId, quality = '128') {
  try {
    const response = await fetch(`${DOWNLOAD_API_BASE}${encodeURIComponent(videoId)}?s=5`);
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
      quality: quality === '320' ? 'high' : 'low',
    };
  } catch (e) {
    console.warn('[YTMusic] Download API unavailable for', videoId, '-', e.message);
    try {
      return await resolveStream(videoId, quality === '320' ? 'high' : 'low', { directOnly: true });
    } catch (streamError) {
      console.warn('[YTMusic] Direct stream fallback unavailable for', videoId, '-', streamError.message);
      return resolveWithYtDlp(videoId, quality === '320' ? 'high' : 'low');
    }
  }
}

async function getAlbum(albumId) {
  const headers = {
    'Content-Type': 'application/json',
    'Origin':       YTM_BASE,
    'Referer':      YTM_BASE + '/',
    'User-Agent':   'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
  };

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

// GET /manifest.json
app.get('/manifest.json', (req, res) => {
  res.json({
    id:          'com.nvmindl.eclipse-ytmusic',
    name:        'YouTube Music',
    version:     '4.1.0-eclipse.1',
    description: 'Stream YouTube Music HLS with refreshed visitor sessions, plus download URLs for Eclipse offline saves.',
    icon:        'https://music.youtube.com/img/favicon_144.png',
    resources:   ['search', 'stream', 'catalog'],
    types:       ['track', 'album'],
    contentType: 'music',
  });
});

// GET /search?q={query}
app.get('/search', async (req, res) => {
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
app.get('/stream/:id', async (req, res) => {
  const videoId = req.params.id;
  // Quality from query param: ?quality=low|high|lossless (default: high)
  const quality = (req.query.quality || 'high').toLowerCase();

  try {
    const result = await resolveStream(videoId, quality);
    res.json(result);
  } catch (e) {
    try {
      const result = await resolveWithYtDlp(videoId, quality);
      res.json(result);
    } catch (fallbackError) {
      console.error('[stream]', videoId, e.message);
      console.error('[stream-fallback]', videoId, fallbackError.message);
      res.status(500).json({ error: e.message });
    }
  }
});

// GET /download/:videoId
// Track-level streamURL targets this endpoint so Eclipse can save tracks
// offline. The updated 8spine module uses y2jar for downloadable files, while
// /stream/:id stays on YouTube Music HLS for playback.
app.get('/download/:id', async (req, res) => {
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
app.get('/audio/:id', (req, res) => {
  const quality = req.query.quality ? `?quality=${encodeURIComponent(req.query.quality)}` : '';
  res.redirect(302, `/download/${encodeURIComponent(req.params.id)}${quality}`);
});

// GET /album/:browseId
// Eclipse calls this when a user taps an album in search results.
// Returns full track listing; Eclipse can bulk-save for offline.
app.get('/album/:id', async (req, res) => {
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
app.get('/', (req, res) => {
  res.json({
    addon:   'Eclipse YouTube Music Addon',
    install: 'Open Eclipse → Settings → Connections → Add Addon → paste: http://localhost:3000/manifest.json',
    docs:    'https://eclipsemusic.app/docs',
  });
});

const PORT = process.env.PORT || 3000;
app.listen(PORT, () => {
  console.log(`\n🎵 Eclipse YouTube Music Addon running on http://localhost:${PORT}`);
  console.log(`   Install in Eclipse: http://localhost:${PORT}/manifest.json\n`);
});
