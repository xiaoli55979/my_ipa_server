#!/usr/bin/env node
// 从 GitHub Releases 拉取所有 IPA/APK/DMG/EXE/ZIP 资产，解析元数据并生成 apps.json + manifest.plist
// DMG(mac) / EXE|ZIP(win) 不解析内容，靠同 Release 里的 IPA/APK 提供 bundleId，版本号用 Release tag
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import zlib from 'node:zlib';
import { fileURLToPath } from 'node:url';
import { execFileSync } from 'node:child_process';
import { createRequire } from 'node:module';
import AdmZip from 'adm-zip';
import simplePlist from 'simple-plist';

const require = createRequire(import.meta.url);
const ApkParser = require('app-info-parser/src/apk');

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const CONFIG = JSON.parse(fs.readFileSync(path.join(ROOT, 'config.json'), 'utf-8'));
const PUBLIC_URL = CONFIG.publicUrl.replace(/\/$/, '');
const REPO = CONFIG.repo;
if (!REPO) { console.error('config.json 缺少 "repo" 字段'); process.exit(1); }

const MANIFEST_DIR = path.join(ROOT, 'docs/manifest');
const ICON_DIR = path.join(ROOT, 'docs/icons');
const APPS_JSON = path.join(ROOT, 'docs/apps.json');
const TMP_DIR = fs.mkdtempSync(path.join(os.tmpdir(), 'ipa-build-'));

function sh(cmd, args) {
  return execFileSync(cmd, args, { encoding: 'utf-8', maxBuffer: 128 * 1024 * 1024 });
}
function escapeXml(s) {
  return String(s).replace(/[<>&"']/g, c => (
    { '<': '&lt;', '>': '&gt;', '&': '&amp;', '"': '&quot;', "'": '&apos;' }[c]
  ));
}
function slugify(s) { return String(s).replace(/[^a-zA-Z0-9._-]/g, '_'); }

// Xcode 把 IPA 里的 PNG 改成 Apple 私有 CgBI 格式(BGRA + 预乘 alpha + 裸 deflate),浏览器不认,转回标准 PNG
const CRC_TABLE = (() => {
  const t = new Uint32Array(256);
  for (let i = 0; i < 256; i++) {
    let c = i;
    for (let k = 0; k < 8; k++) c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1);
    t[i] = c >>> 0;
  }
  return t;
})();
function crc32(buf) {
  let c = 0xffffffff;
  for (let i = 0; i < buf.length; i++) c = CRC_TABLE[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}
function makeChunk(type, data) {
  const typeBuf = Buffer.from(type, 'ascii');
  const lenBuf = Buffer.alloc(4); lenBuf.writeUInt32BE(data.length, 0);
  const crcBuf = Buffer.alloc(4); crcBuf.writeUInt32BE(crc32(Buffer.concat([typeBuf, data])), 0);
  return Buffer.concat([lenBuf, typeBuf, data, crcBuf]);
}
function normalizePng(buf) {
  if (!buf || buf.length < 8 || buf.readUInt32BE(0) !== 0x89504e47) return buf;
  let offset = 8, isCgBI = false, ihdr = null;
  const idats = [], chunks = [];
  while (offset < buf.length) {
    const length = buf.readUInt32BE(offset);
    const type = buf.slice(offset + 4, offset + 8).toString('ascii');
    const data = buf.slice(offset + 8, offset + 8 + length);
    if (type === 'CgBI') isCgBI = true;
    else if (type === 'IDAT') idats.push(data);
    else if (type === 'IEND') { offset += 12 + length; break; }
    else { if (type === 'IHDR') ihdr = data; chunks.push({ type, data }); }
    offset += 12 + length;
  }
  if (!isCgBI || !ihdr) return buf;
  const width = ihdr.readUInt32BE(0);
  const height = ihdr.readUInt32BE(4);
  const bitDepth = ihdr[8];
  const colorType = ihdr[9];
  if (bitDepth !== 8 || (colorType !== 6 && colorType !== 2)) return buf;
  const channels = colorType === 6 ? 4 : 3;

  let raw;
  try { raw = zlib.inflateRawSync(Buffer.concat(idats)); }
  catch {
    try { raw = zlib.inflateSync(Buffer.concat(idats)); }
    catch { return buf; }
  }

  const rowBytes = width * channels;
  const unfiltered = Buffer.alloc(height * rowBytes);
  let src = 0;
  for (let y = 0; y < height; y++) {
    const ft = raw[src++];
    const dstOff = y * rowBytes;
    const prevOff = (y - 1) * rowBytes;
    for (let i = 0; i < rowBytes; i++) {
      const a = i >= channels ? unfiltered[dstOff + i - channels] : 0;
      const b = y > 0 ? unfiltered[prevOff + i] : 0;
      const c = (y > 0 && i >= channels) ? unfiltered[prevOff + i - channels] : 0;
      let r;
      switch (ft) {
        case 0: r = raw[src + i]; break;
        case 1: r = (raw[src + i] + a) & 0xff; break;
        case 2: r = (raw[src + i] + b) & 0xff; break;
        case 3: r = (raw[src + i] + ((a + b) >> 1)) & 0xff; break;
        case 4: {
          const p = a + b - c;
          const pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c);
          const pr = (pa <= pb && pa <= pc) ? a : (pb <= pc) ? b : c;
          r = (raw[src + i] + pr) & 0xff;
          break;
        }
        default: return buf;
      }
      unfiltered[dstOff + i] = r;
    }
    src += rowBytes;
  }

  for (let i = 0; i < unfiltered.length; i += channels) {
    const t = unfiltered[i];
    unfiltered[i] = unfiltered[i + 2];
    unfiltered[i + 2] = t;
    if (channels === 4) {
      const a = unfiltered[i + 3];
      if (a > 0 && a < 255) {
        unfiltered[i]     = Math.min(255, Math.round(unfiltered[i]     * 255 / a));
        unfiltered[i + 1] = Math.min(255, Math.round(unfiltered[i + 1] * 255 / a));
        unfiltered[i + 2] = Math.min(255, Math.round(unfiltered[i + 2] * 255 / a));
      }
    }
  }

  const filtered = Buffer.alloc(height * (1 + rowBytes));
  for (let y = 0; y < height; y++) {
    filtered[y * (1 + rowBytes)] = 0;
    unfiltered.copy(filtered, y * (1 + rowBytes) + 1, y * rowBytes, (y + 1) * rowBytes);
  }
  const recompressed = zlib.deflateSync(filtered);

  const parts = [buf.slice(0, 8)];
  for (const ch of chunks) parts.push(makeChunk(ch.type, ch.data));
  parts.push(makeChunk('IDAT', recompressed));
  parts.push(makeChunk('IEND', Buffer.alloc(0)));
  return Buffer.concat(parts);
}

function fetchReleases() {
  const out = sh('gh', ['api', '--paginate', `/repos/${REPO}/releases?per_page=100`]);
  const arr = JSON.parse(out);
  return arr.filter(r => !r.draft);
}

function downloadAsset(tag, name) {
  const sub = path.join(TMP_DIR, slugify(tag));
  fs.mkdirSync(sub, { recursive: true });
  sh('gh', ['release', 'download', tag,
    '--repo', REPO,
    '--pattern', name,
    '--dir', sub,
    '--clobber']);
  return path.join(sub, name);
}

function parseIpa(filePath) {
  const zip = new AdmZip(filePath);
  const entries = zip.getEntries();
  const infoEntry = entries.find(e => /^Payload\/[^/]+\.app\/Info\.plist$/.test(e.entryName));
  if (!infoEntry) throw new Error('Info.plist not found');
  const appDir = path.posix.dirname(infoEntry.entryName);
  const info = simplePlist.parse(infoEntry.getData());

  const bundleId = info.CFBundleIdentifier;
  const version = info.CFBundleShortVersionString || info.CFBundleVersion || '0.0.0';
  const name = info.CFBundleDisplayName || info.CFBundleName || bundleId;

  const iconFiles =
    info.CFBundleIcons?.CFBundlePrimaryIcon?.CFBundleIconFiles ||
    info['CFBundleIcons~ipad']?.CFBundlePrimaryIcon?.CFBundleIconFiles ||
    (info.CFBundleIconFile ? [info.CFBundleIconFile] : []);

  let iconData = null;
  if (iconFiles.length) {
    const candidates = entries.filter(e => {
      if (!e.entryName.startsWith(appDir + '/')) return false;
      const base = path.posix.basename(e.entryName);
      if (!base.endsWith('.png')) return false;
      return iconFiles.some(n => base.startsWith(n));
    });
    if (candidates.length) {
      candidates.sort((a, b) => b.header.size - a.header.size);
      iconData = normalizePng(candidates[0].getData());
    }
  }
  return { bundleId, version, name, iconData };
}

async function parseApk(filePath) {
  const parser = new ApkParser(filePath);
  const info = await parser.parse();
  const bundleId = info.package;
  const version = info.versionName || String(info.versionCode || '0.0.0');
  let name = bundleId;
  if (typeof info.application?.label === 'string') name = info.application.label;
  else if (Array.isArray(info.application?.label) && info.application.label.length) name = info.application.label[0];
  else if (typeof info.label === 'string') name = info.label;
  else if (Array.isArray(info.label) && info.label.length) name = info.label[0];

  let iconData = null;
  if (info.icon && typeof info.icon === 'string') {
    const m = info.icon.match(/^data:image\/\w+;base64,(.+)$/);
    if (m) iconData = Buffer.from(m[1], 'base64');
  }
  return { bundleId, version, name, iconData };
}

function makeManifest({ bundleId, version, name, ipaUrl }) {
  return `<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>items</key>
  <array>
    <dict>
      <key>assets</key>
      <array>
        <dict>
          <key>kind</key><string>software-package</string>
          <key>url</key><string>${escapeXml(ipaUrl)}</string>
        </dict>
      </array>
      <key>metadata</key>
      <dict>
        <key>bundle-identifier</key><string>${escapeXml(bundleId)}</string>
        <key>bundle-version</key><string>${escapeXml(version)}</string>
        <key>kind</key><string>software</string>
        <key>title</key><string>${escapeXml(name)}</string>
      </dict>
    </dict>
  </array>
</dict>
</plist>
`;
}

function cleanDir(dir) {
  fs.mkdirSync(dir, { recursive: true });
  for (const f of fs.readdirSync(dir)) {
    if (f === '.gitkeep') continue;
    fs.unlinkSync(path.join(dir, f));
  }
}

async function main() {
  cleanDir(MANIFEST_DIR);
  cleanDir(ICON_DIR);

  const releases = fetchReleases();
  console.log(`Found ${releases.length} release(s).`);

  const apps = new Map();

  for (const rel of releases) {
    // 先处理 ipa/apk 拿到 bundleId,再处理 dmg/exe/zip 挂到同一 app
    const rawAssets = rel.assets || [];
    const extOf = (n) => (n.match(/\.(ipa|apk|dmg|exe|zip)$/i) || [])[1]?.toLowerCase() || '';
    const platformOf = (ext) => ext === 'ipa' ? 'ios'
      : ext === 'apk' ? 'android'
      : ext === 'dmg' ? 'mac'
      : (ext === 'exe' || ext === 'zip') ? 'win' : null;
    const rank = (n) => { const p = platformOf(extOf(n)); return (p === 'ios' || p === 'android') ? 0 : p ? 1 : 2; };
    const orderedAssets = rawAssets.slice().sort((a, b) => rank(a.name) - rank(b.name));

    let releaseBundleId = null;
    let releaseAppName = null;

    for (const asset of orderedAssets) {
      const ext = extOf(asset.name);
      const platform = platformOf(ext);
      if (!platform) continue;

      if (platform === 'mac' || platform === 'win') {
        if (!releaseBundleId) {
          console.warn(`[skip] ${ext} ${asset.name}: release ${rel.tag_name} 没有同包名的 ipa/apk，无法归组`);
          continue;
        }
        const pkgUrl = asset.browser_download_url;
        const uploadedAt = asset.updated_at || asset.created_at || rel.published_at;
        if (!apps.has(releaseBundleId)) {
          apps.set(releaseBundleId, {
            id: releaseBundleId, name: releaseAppName || releaseBundleId,
            icon: null, ios: [], android: [], mac: [], win: []
          });
        }
        const app = apps.get(releaseBundleId);
        if (!app.mac) app.mac = [];
        if (!app.win) app.win = [];
        app[platform].push({
          version: rel.tag_name,
          uploadedAt,
          tag: rel.tag_name,
          releaseName: rel.name || rel.tag_name,
          notes: rel.body || '',
          file: asset.name,
          size: asset.size,
          downloadUrl: pkgUrl
        });
        continue;
      }

      const isIpa = ext === 'ipa';

      let localPath;
      try {
        localPath = downloadAsset(rel.tag_name, asset.name);
      } catch (e) {
        console.warn(`[skip] download ${rel.tag_name}/${asset.name}: ${e.message}`);
        continue;
      }

      let parsed;
      try {
        parsed = isIpa ? parseIpa(localPath) : await parseApk(localPath);
      } catch (e) {
        console.warn(`[skip] parse ${asset.name}: ${e.message}`);
        continue;
      }

      const pkgUrl = asset.browser_download_url;
      const uploadedAt = asset.updated_at || asset.created_at || rel.published_at;

      if (!apps.has(parsed.bundleId)) {
        apps.set(parsed.bundleId, {
          id: parsed.bundleId,
          name: parsed.name,
          icon: null,
          ios: [],
          android: [],
          mac: [],
          win: []
        });
      }
      const app = apps.get(parsed.bundleId);
      if (!app.mac) app.mac = [];
      if (!app.win) app.win = [];

      if (!releaseBundleId) { releaseBundleId = parsed.bundleId; releaseAppName = parsed.name; }

      if (parsed.iconData && !app.icon) {
        const iconName = `${slugify(parsed.bundleId)}-${platform}.png`;
        fs.writeFileSync(path.join(ICON_DIR, iconName), parsed.iconData);
        app.icon = `${PUBLIC_URL}/icons/${iconName}`;
      }
      if (parsed.name && parsed.name !== parsed.bundleId) app.name = parsed.name;

      const entry = {
        version: parsed.version,
        uploadedAt,
        tag: rel.tag_name,
        releaseName: rel.name || rel.tag_name,
        notes: rel.body || '',
        file: asset.name,
        size: asset.size,
        downloadUrl: pkgUrl
      };

      if (isIpa) {
        const manifestName = `${slugify(parsed.bundleId)}-${slugify(rel.tag_name)}.plist`;
        fs.writeFileSync(path.join(MANIFEST_DIR, manifestName), makeManifest({
          bundleId: parsed.bundleId, version: parsed.version, name: parsed.name, ipaUrl: pkgUrl
        }));
        entry.manifestUrl = `${PUBLIC_URL}/manifest/${manifestName}`;
        entry.installUrl = `itms-services://?action=download-manifest&url=${encodeURIComponent(entry.manifestUrl)}`;
        app.ios.push(entry);
      } else {
        app.android.push(entry);
      }

      try { fs.unlinkSync(localPath); } catch {}
    }
  }

  const out = [...apps.values()].map(a => {
    if (!a.mac) a.mac = [];
    if (!a.win) a.win = [];
    a.ios.sort((x, y) => y.uploadedAt.localeCompare(x.uploadedAt));
    a.android.sort((x, y) => y.uploadedAt.localeCompare(x.uploadedAt));
    a.mac.sort((x, y) => y.uploadedAt.localeCompare(x.uploadedAt));
    a.win.sort((x, y) => y.uploadedAt.localeCompare(x.uploadedAt));
    const times = [a.ios[0]?.uploadedAt, a.android[0]?.uploadedAt, a.mac[0]?.uploadedAt, a.win[0]?.uploadedAt].filter(Boolean);
    a.latestAt = times.sort().pop() || null;
    return a;
  });
  out.sort((a, b) => (b.latestAt || '').localeCompare(a.latestAt || ''));

  fs.writeFileSync(APPS_JSON, JSON.stringify({
    siteTitle: CONFIG.siteTitle || 'App 分发',
    publicUrl: PUBLIC_URL,
    generatedAt: new Date().toISOString(),
    apps: out
  }, null, 2));

  console.log(`Built ${out.length} app(s).`);
}

main().catch(e => { console.error(e); process.exit(1); });
