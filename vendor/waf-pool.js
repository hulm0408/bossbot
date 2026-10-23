// ---------------------------------------------------------------------------
// WAF TOKEN POOL + CIRCUIT BREAKER  (2026-10-22)
//
// Why this exists:
//   Swiggy's AWS WAF flags our IP when a burst of 29-58 DAPI calls lands
//   repeatedly without a valid `aws-waf-token` cookie. Yesterday's "fast"
//   scans are exactly that burst pattern — that is what got the IP flagged.
//
// Two mechanisms here (together they make scans fast AND keep the IP clean):
//
//  1) SHARED TOKEN POOL
//     One valid `aws-waf-token` (acquired once by headless Chromium, or
//     hydrated from the persistent Cloud Vault) is injected into EVERY
//     DAPI request — all 29 accounts, all scans. With a token, Swiggy's
//     WAF sees normal browser traffic and lets bursts through. The token
//     is persisted in db.json + the encrypted Cloud Vault, so a fresh
//     Render deploy starts WARM (no cold-start challenge storm).
//
//  2) CIRCUIT BREAKER
//     When a 403 / WAF challenge is detected (token expired or IP hot),
//     further bursts STOP — sending more is what keeps the block alive.
//     Cooldown escalates 3 → 5 → 10 min on repeated hits within 30 min,
//     resets after 60 min clean. During cooldown, scans short-circuit with
//     a countdown instead of hammering Swiggy.
// ---------------------------------------------------------------------------

import { getDb, saveDb } from './store.js';

const TOKEN_TTL_MS = 2 * 60 * 60 * 1000;        // a WAF token lives ~hours; 2h refresh budget
const ESCALATION_WINDOW_MS = 30 * 60 * 1000;    // hits within 30 min escalate
const STREAK_RESET_MS = 60 * 60 * 1000;         // 60 min clean → streak back to 0
const HIT_DEBOUNCE_MS = 120 * 1000;             // a scan's burst of 403s = ONE incident
const COOLDOWNS_MS = [3 * 60 * 1000, 5 * 60 * 1000, 10 * 60 * 1000];

const state = {
  token: '',
  acquiredAt: 0,
  source: '',          // 'chromium' | 'vault' | 'manual'
  cooldownUntil: 0,
  hitStreak: 0,
  windowStart: 0
};
let lastHitAt = 0;

function persist() {
  try {
    const db = getDb();
    db.waf = {
      token: state.token,
      acquiredAt: state.acquiredAt,
      source: state.source,
      cooldownUntil: state.cooldownUntil,
      hitStreak: state.hitStreak,
      windowStart: state.windowStart
    };
    saveDb(db);
  } catch { /* persistence is best-effort */ }
}

// Seed/replace the shared token (from Chromium acquisition or a manual paste).
export function seedToken(token, { source = 'manual', acquiredAt = Date.now() } = {}) {
  const t = String(token || '').trim();
  if (t.length <= 50) return false; // a real aws-waf-token is long; reject junk
  state.token = t;
  state.acquiredAt = Number(acquiredAt) || Date.now();
  state.source = source;
  persist();
  return true;
}

// Synchronous, network-free access for request builders.
export function getTokenSync() {
  if (!state.token || state.token.length <= 50) return '';
  if (Date.now() - state.acquiredAt > TOKEN_TTL_MS) return '';
  return state.token;
}

export function tokenAgeMs() {
  return state.token ? Math.max(0, Date.now() - state.acquiredAt) : 0;
}

export function isStale() {
  return Boolean(state.token && !getTokenSync());
}

// Restore persisted state at boot (db.json first; the Cloud Vault hydrate
// in store.js may then overwrite with a newer token).
export function loadFromDb() {
  try {
    const w = getDb()?.waf || null;
    if (w && typeof w.token === 'string' && w.token.length > 50) {
      state.token = w.token;
      state.acquiredAt = Number(w.acquiredAt) || 0;
      state.source = w.source || 'vault';
    }
    if (Number(w?.cooldownUntil) > Date.now()) {
      state.cooldownUntil = Number(w.cooldownUntil);
      state.hitStreak = Number(w.hitStreak) || 0;
      state.windowStart = Number(w.windowStart) || 0;
    }
  } catch { /* ignore */ }
}

// Record a WAF block. Escalating cooldown with debounce:
//   one scan producing 29 × 403 in 30s counts as a single hit.
export function markWafHit() {
  const now = Date.now();
  if (lastHitAt && now - lastHitAt < HIT_DEBOUNCE_MS) {
    // Same incident (burst of 403s from one scan) — keep/extend current cooldown.
    const dur = COOLDOWNS_MS[Math.max(0, Math.min(state.hitStreak, COOLDOWNS_MS.length) - 1)] || COOLDOWNS_MS[0];
    if (now > state.cooldownUntil) state.cooldownUntil = now + dur;
    persist();
    return;
  }
  lastHitAt = now;
  if (!state.windowStart || now - state.windowStart > ESCALATION_WINDOW_MS || now - state.windowStart > STREAK_RESET_MS) {
    state.hitStreak = 0;
    state.windowStart = now;
  }
  state.hitStreak = Math.min(state.hitStreak + 1, COOLDOWNS_MS.length);
  state.cooldownUntil = now + COOLDOWNS_MS[state.hitStreak - 1];
  persist();
}

export function cooldownRemainingMs() {
  return Math.max(0, state.cooldownUntil - Date.now());
}

export function clearCooldown() {
  state.cooldownUntil = 0;
  state.hitStreak = 0;
  state.windowStart = 0;
  persist();
}

// Human summary for the boss `/waf` command.
export function getSummary() {
  const now = Date.now();
  return {
    hasToken: Boolean(getTokenSync()),
    stale: isStale(),
    tokenAgeMin: state.token ? Math.round((now - state.acquiredAt) / 60000) : null,
    source: state.source || 'none',
    cooldownMin: Math.ceil(cooldownRemainingMs() / 60000)
  };
}
