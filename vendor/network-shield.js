import dns from 'dns';
import http from 'http';
import https from 'https';

// ============================================================================
// CLOUD / RENDER DOCKER IPv4-FIRST + KEEP-ALIVE + TELEGRAM AUTO-RETRY SHIELD
// ============================================================================
// Root Cause Eliminated:
//   On Render / Linux cloud containers, `api.telegram.org`, `nominatim.openstreetmap.org`,
//   and CDN dual-stack endpoints publish both IPv4 (`149.154.166.110`) and IPv6
//   (`2001:67c:4e8:f004::9`). Outbound IPv6 packets drop silently inside cloud
//   NAT without ICMPv6 unreachable, causing:
//     1) `node-fetch` `ClientRequest` `ETIMEDOUT` after ~75-127s on `answerCallbackQuery` / `sendMessage`
//     2) Telegraf `p-timeout` `Promise timed out after 90000 milliseconds`
//
// Forcing IPv4 (`family: 4`) globally at process boot + wrapping `bot.telegram.callApi`
// with per-request `AbortController` timeouts + instant 3x retries + non-fatal
// `answerCallbackQuery` absorption permanently prevents both errors!

let shieldInstalled = false;

export function installGlobalIpv4NetworkShield() {
  if (shieldInstalled) return;
  shieldInstalled = true;

  try {
    if (typeof dns.setDefaultResultOrder === 'function') {
      dns.setDefaultResultOrder('ipv4first');
    }
  } catch {}

  // Override `dns.lookup` so BOTH `https.Agent` (`node-fetch` / Telegraf) AND Node's
  // native `undici` (`globalThis.fetch`) resolve IPv4 (`family: 4`) first whenever an
  // explicit `family: 6` was not requested, automatically falling back to dual-stack
  // ONLY if a hostname truly has zero IPv4 `A` records.
  const origLookup = dns.lookup.bind(dns);
  dns.lookup = function ipv4PreferredLookup(hostname, options, callback) {
    if (typeof options === 'function') {
      callback = options;
      options = {};
    } else if (typeof options === 'number') {
      options = { family: options };
    } else {
      options = { ...(options || {}) };
    }

    // Preserve `{ all: true }` lookups (`undici` Happy Eyeballs) by sorting IPv4 records ahead of IPv6 AND filtering blackholed IPv6 when IPv4 exists!
    if (options.all) {
      return origLookup(hostname, options, (err, addresses) => {
        if (err || !Array.isArray(addresses)) return callback(err, addresses);
        const v4 = addresses.filter(a => a && a.family === 4);
        return callback(null, v4.length > 0 ? v4 : addresses);
      });
    }

    if (options.family && options.family !== 0) {
      return origLookup(hostname, options, callback);
    }

    return origLookup(hostname, { ...options, family: 4 }, (err, address, family) => {
      if (!err && address) {
        return callback(null, address, family || 4);
      }
      return origLookup(hostname, options, callback);
    });
  };

  if (http.globalAgent) {
    http.globalAgent.keepAlive = true;
  }
  if (https.globalAgent) {
    https.globalAgent.keepAlive = true;
    https.globalAgent.options.family = 4;
  }
}

// Install immediately the instant this module is imported!
installGlobalIpv4NetworkShield();

export function createIpv4TelegramAgent() {
  return new https.Agent({
    family: 4,
    keepAlive: true,
    keepAliveMsecs: 15000,
    maxSockets: 64,
    maxFreeSockets: 16,
    timeout: 12000
  });
}

function isTransientTelegramNetworkError(err) {
  if (!err) return false;
  const code = String(err.code || err.errno || '').toUpperCase();
  const msg = String(err.message || err.description || '');
  if (['ETIMEDOUT', 'ECONNRESET', 'ECONNREFUSED', 'EPIPE', 'EAI_AGAIN', 'ENOTFOUND', 'UND_ERR_CONNECT_TIMEOUT', 'ABORT_ERR'].includes(code)) {
    return true;
  }
  if (/ETIMEDOUT|ECONNRESET|socket hang up|network timeout|aborted|reason:\s*$|502 Bad Gateway|503 Service|504 Gateway/i.test(msg)) {
    return true;
  }
  return false;
}

export function installBulletproofTelegramTransport(bot) {
  if (!bot?.telegram || bot.telegram.__ipv4RetryShieldInstalled) return bot;
  bot.telegram.__ipv4RetryShieldInstalled = true;

  // Ensure Telegraf's underlying agent is strictly IPv4 keep-alive
  bot.telegram.options.agent = createIpv4TelegramAgent();

  const rawCallApi = bot.telegram.callApi.bind(bot.telegram);

  bot.telegram.callApi = async function shieldedCallApi(method, payload, callOpts = {}) {
    const isMediaUpload = /sendPhoto|sendDocument|sendVideo|sendMediaGroup|editMessageMedia/i.test(String(method));
    const isCallbackAck = method === 'answerCallbackQuery';
    const perAttemptMs = isCallbackAck ? 6500 : (isMediaUpload ? 25000 : 12000);
    const maxAttempts = isCallbackAck ? 2 : 3;

    let lastErr = null;
    for (let attempt = 1; attempt <= maxAttempts; attempt++) {
      const controller = new AbortController();
      const timer = setTimeout(() => controller.abort(), perAttemptMs);
      if (typeof timer.unref === 'function') timer.unref();

      try {
        const mergedOpts = {
          ...(callOpts || {}),
          signal: callOpts?.signal || controller.signal
        };
        const out = await rawCallApi(method, payload, mergedOpts);
        clearTimeout(timer);
        return out;
      } catch (err) {
        clearTimeout(timer);
        lastErr = err;

        // Benign Telegram callback states (`query is too old`, `message is not modified`)
        const desc = String(err?.description || err?.message || '');
        if (isCallbackAck && /query is too old|query ID is invalid/i.test(desc)) {
          return true;
        }

        if (attempt < maxAttempts && isTransientTelegramNetworkError(err)) {
          // Rotate fresh IPv4 socket pool if a keep-alive socket went stale across cloud NAT idle timeout
          bot.telegram.options.agent = createIpv4TelegramAgent();
          await new Promise(r => setTimeout(r, 150 * attempt));
          continue;
        }
        break;
      }
    }

    // NEVER let a cosmetic spinner acknowledgment (`answerCallbackQuery`) crash an order action into `[AI-DIAG]`!
    if (isCallbackAck) {
      console.warn(`[TelegramShield] Non-fatal answerCallbackQuery warning absorbed: ${lastErr?.message || lastErr}`);
      return true;
    }

    throw lastErr;
  };

  return bot;
}
