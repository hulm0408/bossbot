import zlib from 'node:zlib';
import crypto from 'node:crypto';

// No hardcoded default: a cloud vault must always be an explicit choice, otherwise
// a new deployment would silently write sessions into another project's repo.
const VAULT_OWNER = process.env.GITHUB_VAULT_OWNER || '';
const VAULT_REPO = process.env.GITHUB_VAULT_REPO || '';
const VAULT_BRANCH = process.env.GITHUB_VAULT_BRANCH || 'bot-vault';
const VAULT_PATH = 'vault/accounts-vault.json';

// SECURITY (2026-10-22 incident): a GitHub PAT was previously XOR-masked and
// hardcoded in this public repo — anyone with read access could reconstruct
// it. Tokens now come EXCLUSIVELY from environment variables (Render env).
// Never embed credentials in source, even obfuscated.
let _noTokenWarned = false;
export function resolveVaultToken() {
  const fromEnv = (process.env.GITHUB_VAULT_TOKEN || process.env.GH_VAULT_TOKEN || '').trim();
  if (!VAULT_OWNER || !VAULT_REPO) return '';
  if (fromEnv) return fromEnv;
  if (process.env.DISABLE_CLOUD_VAULT === '1') return '';
  if (!_noTokenWarned) {
    _noTokenWarned = true;
    console.warn('[CloudVault] GITHUB_VAULT_TOKEN env not set — cloud vault sync disabled (set it in Render env; NEVER embed tokens in source).');
  }
  return '';
}

// ── Vault-at-rest encryption (AES-256-GCM) ──────────────────────────────────
// The vault payload (raw Swiggy cookies/tids/tokens) is encrypted before it
// is ever written to the `bot-vault` branch. Key = scrypt(VAULT_ENCRYPTION_KEY
// env). Legacy plaintext files still hydrate fine and get re-encrypted on the
// next push (self-healing).
const VAULT_ENC_MARKER = 'v2-aes256gcm';
const VAULT_ENC_SALT = 'sacha-beta-vault-salt-v2';

function vaultEncryptionKey() {
  const raw = (process.env.VAULT_ENCRYPTION_KEY || '').trim();
  if (!raw) return null;
  return crypto.scryptSync(raw, VAULT_ENC_SALT, 32);
}

let _noEncKeyWarned = false;
function encryptVaultPayloadText(payloadObj) {
  const key = vaultEncryptionKey();
  const plain = JSON.stringify(payloadObj);
  if (!key) {
    if (!_noEncKeyWarned) {
      _noEncKeyWarned = true;
      console.warn('[CloudVault] VAULT_ENCRYPTION_KEY env not set — pushing vault UNENCRYPTED (set it in Render env).');
    }
    return plain;
  }
  const iv = crypto.randomBytes(12);
  const cipher = crypto.createCipheriv('aes-256-gcm', key, iv);
  const enc = Buffer.concat([cipher.update(plain, 'utf8'), cipher.final()]);
  return JSON.stringify({
    __vaultEnc: VAULT_ENC_MARKER,
    iv: iv.toString('hex'),
    tag: cipher.getAuthTag().toString('hex'),
    data: enc.toString('hex')
  });
}

export function decryptVaultPayloadText(rawText) {
  let obj;
  try { obj = JSON.parse(rawText); } catch (err) { throw new Error(`vault payload is not JSON: ${err.message}`); }
  if (!obj || obj.__vaultEnc !== VAULT_ENC_MARKER) return obj; // legacy plaintext → pass through
  const key = vaultEncryptionKey();
  if (!key) {
    console.warn('[CloudVault] vault file is encrypted but VAULT_ENCRYPTION_KEY env is missing — cannot decrypt.');
    return null;
  }
  try {
    const decipher = crypto.createDecipheriv('aes-256-gcm', key, Buffer.from(obj.iv, 'hex'));
    decipher.setAuthTag(Buffer.from(obj.tag, 'hex'));
    const dec = Buffer.concat([decipher.update(Buffer.from(obj.data, 'hex')), decipher.final()]);
    return JSON.parse(dec.toString('utf8'));
  } catch (err) {
    console.warn('[CloudVault] vault decrypt failed (wrong VAULT_ENCRYPTION_KEY?):', err.message);
    return null;
  }
}

function ghHeaders(token) {
  return {
    Authorization: `Bearer ${token}`,
    Accept: 'application/vnd.github+json',
    'Content-Type': 'application/json',
    'X-GitHub-Api-Version': '2022-11-28',
    'User-Agent': 'sacha-beta-vault-sync/15.0'
  };
}

let pushDebounceTimer = null;
let pushInFlight = Promise.resolve();
let latestSnapshotSupplier = null;
let cloudVaultHydrated = false;

/**
 * Extracts all `.json` / `.txt` text entries from a ZIP buffer using pure built-in Node `zlib`
 * (supports Store method 0 and Deflate method 8 — covers 99.9% of all desktop/mobile ZIPs!).
 */
export function extractSessionFilesFromZipBuffer(zipBuf) {
  const results = [];
  if (!Buffer.isBuffer(zipBuf) || zipBuf.length < 22) return results;

  // Walk Local File Headers (`PK\x03\x04` = 0x04034b50)
  let offset = 0;
  while (offset + 30 <= zipBuf.length) {
    const sig = zipBuf.readUInt32LE(offset);
    if (sig !== 0x04034b50) {
      offset++;
      continue;
    }
    const flags = zipBuf.readUInt16LE(offset + 6);
    const method = zipBuf.readUInt16LE(offset + 8);
    const compSize = zipBuf.readUInt32LE(offset + 18);
    const nameLen = zipBuf.readUInt16LE(offset + 26);
    const extraLen = zipBuf.readUInt16LE(offset + 28);
    const nameStart = offset + 30;
    const dataStart = nameStart + nameLen + extraLen;

    if (nameStart + nameLen > zipBuf.length) break;
    const entryName = zipBuf.subarray(nameStart, nameStart + nameLen).toString('utf8');

    // Data descriptor flag (bit 3): if `compSize === 0`, skip cleanly to Central Directory fallback below
    if ((flags & 0x08) === 0 && dataStart + compSize <= zipBuf.length) {
      if (!entryName.endsWith('/') && !entryName.includes('__MACOSX') && /\.(json|txt|cookies?)$/i.test(entryName)) {
        try {
          const rawSlice = zipBuf.subarray(dataStart, dataStart + compSize);
          const contentBuf = method === 0
            ? rawSlice
            : (method === 8 ? zlib.inflateRawSync(rawSlice) : null);
          if (contentBuf && contentBuf.length > 0) {
            results.push({ fileName: entryName, text: contentBuf.toString('utf8') });
          }
        } catch {}
      }
      offset = dataStart + compSize;
    } else {
      offset = dataStart;
    }
  }

  // Fallback via Central Directory (`PK\x01\x02` = 0x02014b50) for streamed ZIPs with bit-3 data descriptors!
  if (results.length === 0) {
    let cdOffset = 0;
    while (cdOffset + 46 <= zipBuf.length) {
      if (zipBuf.readUInt32LE(cdOffset) !== 0x02014b50) {
        cdOffset++;
        continue;
      }
      const method = zipBuf.readUInt16LE(cdOffset + 10);
      const compSize = zipBuf.readUInt32LE(cdOffset + 20);
      const nameLen = zipBuf.readUInt16LE(cdOffset + 28);
      const extraLen = zipBuf.readUInt16LE(cdOffset + 30);
      const commentLen = zipBuf.readUInt16LE(cdOffset + 32);
      const localHdrOffset = zipBuf.readUInt32LE(cdOffset + 42);
      const entryName = zipBuf.subarray(cdOffset + 46, cdOffset + 46 + nameLen).toString('utf8');

      if (!entryName.endsWith('/') && !entryName.includes('__MACOSX') && /\.(json|txt|cookies?)$/i.test(entryName)) {
        try {
          const lNameLen = zipBuf.readUInt16LE(localHdrOffset + 26);
          const lExtraLen = zipBuf.readUInt16LE(localHdrOffset + 28);
          const lDataStart = localHdrOffset + 30 + lNameLen + lExtraLen;
          const rawSlice = zipBuf.subarray(lDataStart, lDataStart + compSize);
          const contentBuf = method === 0
            ? rawSlice
            : (method === 8 ? zlib.inflateRawSync(rawSlice) : null);
          if (contentBuf && contentBuf.length > 0) {
            results.push({ fileName: entryName, text: contentBuf.toString('utf8') });
          }
        } catch {}
      }
      cdOffset += 46 + nameLen + extraLen + commentLen;
    }
  }

  return results;
}

async function ensureOrphanVaultBranchExists(token) {
  const refUrl = `https://api.github.com/repos/${VAULT_OWNER}/${VAULT_REPO}/git/ref/heads/${VAULT_BRANCH}`;
  const refRes = await fetch(refUrl, { headers: ghHeaders(token), signal: AbortSignal.timeout(8000) });
  if (refRes.status === 200) return true;

  // Create a true standalone orphan commit on `refs/heads/bot-vault` (never triggers `main` Render deploys!)
  const blobRes = await fetch(`https://api.github.com/repos/${VAULT_OWNER}/${VAULT_REPO}/git/blobs`, {
    method: 'POST',
    headers: ghHeaders(token),
    body: JSON.stringify({ content: JSON.stringify({ version: 15, accounts: {}, deletedAccounts: {}, sessionVault: {} }, null, 2), encoding: 'utf-8' }),
    signal: AbortSignal.timeout(8000)
  });
  if (!blobRes.ok) return false;
  const blob = await blobRes.json();

  const treeRes = await fetch(`https://api.github.com/repos/${VAULT_OWNER}/${VAULT_REPO}/git/trees`, {
    method: 'POST',
    headers: ghHeaders(token),
    body: JSON.stringify({ tree: [{ path: VAULT_PATH, mode: '100644', type: 'blob', sha: blob.sha }] }),
    signal: AbortSignal.timeout(8000)
  });
  if (!treeRes.ok) return false;
  const tree = await treeRes.json();

  const commitRes = await fetch(`https://api.github.com/repos/${VAULT_OWNER}/${VAULT_REPO}/git/commits`, {
    method: 'POST',
    headers: ghHeaders(token),
    body: JSON.stringify({ message: 'chore(vault): initialize persistent account vault branch', tree: tree.sha, parents: [] }),
    signal: AbortSignal.timeout(8000)
  });
  if (!commitRes.ok) return false;
  const commit = await commitRes.json();

  const createRefRes = await fetch(`https://api.github.com/repos/${VAULT_OWNER}/${VAULT_REPO}/git/refs`, {
    method: 'POST',
    headers: ghHeaders(token),
    body: JSON.stringify({ ref: `refs/heads/${VAULT_BRANCH}`, sha: commit.sha }),
    signal: AbortSignal.timeout(8000)
  });
  return createRefRes.ok || createRefRes.status === 422;
}

export async function pullAccountsFromCloudVault() {
  const token = resolveVaultToken();
  if (!token) return null;

  try {
    const url = `https://api.github.com/repos/${VAULT_OWNER}/${VAULT_REPO}/contents/${VAULT_PATH}?ref=${encodeURIComponent(VAULT_BRANCH)}`;
    const res = await fetch(url, { headers: ghHeaders(token), signal: AbortSignal.timeout(8000) });
    if (!res.ok) return null;
    const meta = await res.json();
    if (!meta?.content) return null;
    const raw = Buffer.from(meta.content.replace(/\s+/g, ''), 'base64').toString('utf8');
    return decryptVaultPayloadText(raw);
  } catch (err) {
    console.warn('[CloudVault] Pull skipped:', err.message);
    return null;
  }
}

export async function pushAccountsToCloudVaultNow(payloadObj) {
  const token = resolveVaultToken();
  if (!token || !payloadObj) return { ok: false, reason: 'NO_TOKEN' };

  pushInFlight = pushInFlight.then(async () => {
    try {
      await ensureOrphanVaultBranchExists(token);
      const url = `https://api.github.com/repos/${VAULT_OWNER}/${VAULT_REPO}/contents/${VAULT_PATH}`;
      const existingRes = await fetch(`${url}?ref=${encodeURIComponent(VAULT_BRANCH)}`, {
        headers: ghHeaders(token),
        signal: AbortSignal.timeout(8000)
      });
      const existingJson = existingRes.ok ? await existingRes.json().catch(() => null) : null;
      const body = {
        message: `chore(vault): sync ${Object.keys(payloadObj.accounts || {}).length} saved Swiggy accounts`,
        content: Buffer.from(encryptVaultPayloadText(payloadObj), 'utf8').toString('base64'),
        branch: VAULT_BRANCH,
        ...(existingJson?.sha ? { sha: existingJson.sha } : {})
      };
      const putRes = await fetch(url, {
        method: 'PUT',
        headers: ghHeaders(token),
        body: JSON.stringify(body),
        signal: AbortSignal.timeout(10000)
      });
      return { ok: putRes.ok, status: putRes.status };
    } catch (err) {
      console.warn('[CloudVault] Push warning:', err.message);
      return { ok: false, error: err.message };
    }
  });
  return pushInFlight;
}

export function scheduleCloudVaultSync(snapshotSupplier, delayMs = 900) {
  if (process.env.DISABLE_CLOUD_VAULT === '1') return;
  latestSnapshotSupplier = snapshotSupplier;
  if (pushDebounceTimer) clearTimeout(pushDebounceTimer);
  pushDebounceTimer = setTimeout(() => {
    pushDebounceTimer = null;
    try {
      const payload = typeof latestSnapshotSupplier === 'function' ? latestSnapshotSupplier() : null;
      if (payload) {
        pushAccountsToCloudVaultNow(payload).catch(() => {});
      }
    } catch {}
  }, delayMs);
  if (typeof pushDebounceTimer.unref === 'function') {
    pushDebounceTimer.unref();
  }
}

export function cancelScheduledCloudVaultSync() {
  if (pushDebounceTimer) {
    clearTimeout(pushDebounceTimer);
    pushDebounceTimer = null;
  }
}

export function isCloudVaultHydrated() {
  return cloudVaultHydrated;
}

export function markCloudVaultHydrated() {
  cloudVaultHydrated = true;
}
