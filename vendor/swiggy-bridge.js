import fs from 'fs';
import path from 'path';
import os from 'os';
import crypto from 'crypto';
import puppeteer from 'puppeteer-core';
import { updateAccount, getNextAutoUserName, cleanEssentialSwiggyCookies } from './store.js';
import { normalizeIndianMobileNumber } from './phone-utils.js';
import * as wafPool from './waf-pool.js';

export function findChromePath() {
  if (process.env.PUPPETEER_EXECUTABLE_PATH) return process.env.PUPPETEER_EXECUTABLE_PATH;
  if (process.env.CHROME_BIN) return process.env.CHROME_BIN;
  if (process.platform === 'win32') {
    return 'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe';
  }
  const linuxPaths = [
    '/usr/bin/chromium',
    '/usr/bin/chromium-browser',
    '/usr/bin/google-chrome',
    '/usr/bin/google-chrome-stable',
    '/opt/playwright/browsers/chromium-1247/chrome-linux64/chrome'
  ];
  for (const p of linuxPaths) {
    try { if (fs.existsSync(p)) return p; } catch (e) {}
  }
  for (const rootDir of ['/opt/playwright/browsers', path.join(os.homedir(), '.cache', 'puppeteer'), '/root/.cache/puppeteer']) {
    try {
      if (!fs.existsSync(rootDir)) continue;
      for (const entry of fs.readdirSync(rootDir)) {
        for (const sub of ['chrome-linux64/chrome', 'chrome-linux/chrome']) {
          const full = path.join(rootDir, entry, sub);
          if (fs.existsSync(full)) return full;
        }
      }
    } catch (e) {}
  }
  return '/usr/bin/chromium';
}

const CHROME_PATH = findChromePath();
const IS_LINUX = process.platform === 'linux';
const HEADLESS_MODE = (IS_LINUX || process.env.RAILWAY_ENVIRONMENT || process.env.HEADLESS === 'true') ? 'new' : false;

// Active login sessions keyed by userId:
// { [userId]: { browser, page, phone, otp, targetAcc, targetAccName, signupEmail, isNewUser, safetyTimer } }
const activeSessions = {};
// Dedicated in-memory session map for Swiggy account deletions (strictly isolated from login)
const activeDeleteSessions = {};
let deleteOtpRequestCount = 0;
let deleteVerifyRequestCount = 0;

// Pre-warmed browser pool for instantaneous (<1s) OTP dispatch
let prewarmedBrowser = null;
let prewarmedPage = null;
let isPrewarming = false;
let prewarmedAt = 0;
let latestSharedWafToken = '';
let latestSharedWafAt = 0;
let wafSolvePromise = null;
const WAF_CACHE_TTL_MS = 8 * 60 * 1000; // 8 minutes

const SWIGGY_WAF_COOKIE_WAIT_MS = 15000;
const SWIGGY_WAF_COOKIE_POLL_MS = 250;
const AUTH_PAGE_EVALUATE_TIMEOUT_MS = 9000;

async function waitForSwiggyWafCookie(page, timeoutMs = SWIGGY_WAF_COOKIE_WAIT_MS) {
  const deadline = Date.now() + Math.max(0, Number(timeoutMs) || 0);
  while (Date.now() < deadline) {
    const cookies = await page.cookies().catch(() => []);
    const wafCookie = cookies.find(cookie => cookie.name === 'aws-waf-token' && String(cookie.value || '').length > 50);
    if (wafCookie) return wafCookie.value;
    const remainingMs = deadline - Date.now();
    if (remainingMs > 0) {
      await new Promise(resolve => setTimeout(resolve, Math.min(SWIGGY_WAF_COOKIE_POLL_MS, remainingMs)));
    }
  }
  return '';
}

async function waitForSwiggyLoginCookies(page, timeoutMs = 800) {
  const deadline = Date.now() + Math.max(0, Number(timeoutMs) || 0);
  let cookies = [];
  do {
    cookies = await page.cookies().catch(() => []);
    if (checkLoggedInFromCookies(cookies)) return cookies;
    const remainingMs = deadline - Date.now();
    if (remainingMs <= 0) break;
    await new Promise(resolve => setTimeout(resolve, Math.min(100, remainingMs)));
  } while (Date.now() < deadline);
  return cookies;
}

export function stripStaleWafCookie(cookieStr = '') {
  if (!cookieStr || typeof cookieStr !== 'string') return '';
  return cookieStr
    .split(';')
    .map(s => s.trim())
    .filter(s => s && !s.startsWith('aws-waf-token='))
    .join('; ');
}

function mergeSetCookiesIntoJar(existingCookieStr = '', setCookieHeaders = []) {
  const map = new Map();
  for (const part of stripStaleWafCookie(existingCookieStr).split(';')) {
    const trimmed = part.trim();
    if (!trimmed || !trimmed.includes('=')) continue;
    const idx = trimmed.indexOf('=');
    map.set(trimmed.slice(0, idx).trim(), trimmed.slice(idx + 1).trim());
  }
  for (const raw of (setCookieHeaders || [])) {
    const first = String(raw || '').split(';')[0].trim();
    if (!first || !first.includes('=')) continue;
    const idx = first.indexOf('=');
    const k = first.slice(0, idx).trim();
    const v = first.slice(idx + 1).trim();
    if (k && v && k !== '_guest_tid' && k !== 'aws-waf-token') {
      map.set(k, v);
    }
  }
  return Array.from(map.entries()).map(([k, v]) => `${k}=${v}`).join('; ');
}

// Helper to decode JWT payload safely
export function decodeJwtPayload(jwtToken) {
  if (!jwtToken || typeof jwtToken !== 'string') return null;
  try {
    const parts = jwtToken.split('.');
    if (parts.length < 2) return null;
    const jsonStr = Buffer.from(parts[1], 'base64').toString('utf-8');
    return JSON.parse(jsonStr);
  } catch (e) {
    return null;
  }
}

export function sanitizeSwiggyName(name) {
  if (!name) return 'Rahul Kumar';
  // Strip any previously appended "(User 1)" or "(6296591407)" tag first
  const withoutSlotTag = String(name).replace(/\([^)]*\)/g, ' ');
  const cleaned = withoutSlotTag.replace(/[^\p{L}\p{M}\p{N}\s]/gu, '').replace(/\s+/g, ' ').trim();
  if ([...cleaned].length < 2 || !/\p{L}/u.test(cleaned) || /^user\s*\d*$/i.test(cleaned)) {
    return 'Rahul Kumar';
  }
  return cleaned;
}

function generateUniqueSwiggyEmail(phone, name) {
  const prefix = String(name || 'rahul').toLowerCase().replace(/[^a-z]/g, '').slice(0, 8) || 'rahul';
  const last4 = String(phone || '').slice(-4) || '1000';
  const rand = Math.floor(1000 + Math.random() * 9000);
  return `${prefix}${last4}.${rand}@gmail.com`;
}

// Helper to check if cookies or account contain a verified logged-in user
export function checkLoggedInFromCookies(input) {
  if (!input) return false;
  let tidValue = '';
  let sessionTid = '';
  let tokenVal = '';
  let isLoggedFlag = '';

  if (typeof input === 'object' && !Array.isArray(input)) {
    if (input.isLoggedIn === false) return false;
    if (input.tid) tidValue = String(input.tid);
    if (input._session_tid || input.session_tid || input.sessionTid) {
      sessionTid = String(input._session_tid || input.session_tid || input.sessionTid);
    }
    if (!sessionTid && tidValue && !tidValue.includes('.')) {
      sessionTid = tidValue;
    }
    if (input.token || input.auth_token || input.access_token || input.authToken || input.accessToken) {
      tokenVal = String(input.token || input.auth_token || input.access_token || input.authToken || input.accessToken);
    }
    if (input.cookies) input = input.cookies;
    else if (!tidValue && !tokenVal && !sessionTid) return Boolean(input.isLoggedIn);
  }

  if (Array.isArray(input)) {
    const getC = (n) => input.find(c => c && c.name === n)?.value || '';
    tidValue = tidValue || getC('tid');
    sessionTid = sessionTid || getC('_session_tid');
    tokenVal = tokenVal || getC('token');
    isLoggedFlag = getC('_is_logged_in');
  } else if (typeof input === 'string') {
    const getS = (re) => {
      const m = input.match(re);
      return m ? decodeURIComponent(m[1]).trim() : '';
    };
    tidValue = tidValue || getS(/(?:^|;\s*)tid=([^;]+)/);
    sessionTid = sessionTid || getS(/(?:^|;\s*)_session_tid=([^;]+)/);
    tokenVal = tokenVal || getS(/(?:^|;\s*)token=([^;]+)/);
    isLoggedFlag = getS(/(?:^|;\s*)_is_logged_in=([^;]+)/);
    if (!tidValue && input.includes('.') && input.length > 50 && !input.includes(';')) {
      tidValue = input.trim();
    }
    if (!sessionTid && /^[0-9a-fA-F]{40,}$/.test(input.trim())) {
      sessionTid = input.trim();
    }
  }

  if (tidValue && tidValue.includes('.')) {
    const payload = decodeJwtPayload(tidValue);
    if (payload && payload.user_id && payload.user_id !== '0' && payload.user_id !== '-1') {
      return true;
    }
    // If `tid` is an explicit guest pre-OTP JWT (`user_id === "0"`) and there is NO real `_session_tid`, it is NOT logged in!
    if (payload && (payload.user_id === '0' || payload.user_id === '-1') && !sessionTid && (!tokenVal || tokenVal === tidValue)) {
      return false;
    }
  }

  if (isLoggedFlag === '1' && (sessionTid.length >= 16 || tokenVal.length >= 10)) {
    return true;
  }
  if (isLoggedFlag !== '0' && (sessionTid.length >= 32 || tokenVal.length >= 24 || (tokenVal.length >= 16 && tidValue.length >= 50))) {
    return true;
  }

  return false;
}

// ---------------------------------------------------------------------------
// Auto-claim & 14-Day Advance Pre-Book Swiggy Event Offers:
// 1. Breakfast Morning (`book-your-offer` — voting before 05:00 IST, redeem 07:00–11:00 IST)
// 2. Late Night Offer (`pick-your-late-night-offer` — voting before 18:30 IST, redeem 21:00–06:00 IST)
// Locks in TODAY + ALL NEXT 14 UPCOMING DAYS in advance via `POST` + `PATCH` on `events.swiggy.com/api/notify`
// so Swiggy's daily batch cutoff (`18:30 IST` LN / `05:00 IST` BF) NEVER misses crediting Free Cash / Coupons!
// ---------------------------------------------------------------------------
export const EVENT_OFFER_OPTIONS = {
  1: { value: 1, shortLabel: '₹50 Free Cash (>₹199)', fullLabel: '₹ ₹50 Free Cash (MOV ₹199 • Stacks Over Coupons)' },
  2: { value: 2, shortLabel: '₹150 OFF Coupon (>₹249)', fullLabel: '# ₹150 OFF Coupon (MOV ₹249)' },
  3: { value: 3, shortLabel: '₹175 LN / ₹100 BF Coupon', fullLabel: '! ₹175 OFF LN (>₹399) / ₹100 OFF BF' },
  4: { value: 4, shortLabel: '₹100 OFF Coupon (>₹149)', fullLabel: '! ₹100 OFF Coupon (MOV ₹149)' }
};

const offerClaimCache = new Map(); // `${accSig}:${offerValue}` -> { result, ts }
const OFFER_CLAIM_TTL_MS = 30 * 60 * 1000;

let cachedEventCampaignMeta = null;
let cachedEventCampaignMetaAt = 0;
const EVENT_META_TTL_MS = 15 * 60 * 1000;

function decodeJwtExpSec(jwt) {
  if (!jwt || typeof jwt !== 'string' || !jwt.includes('.')) return 0;
  const payload = decodeJwtPayload(jwt);
  return Number(payload?.exp || 0);
}

async function getLiveEventCampaignMeta(forceRefresh = false) {
  if (!forceRefresh && cachedEventCampaignMeta && (Date.now() - cachedEventCampaignMetaAt < EVENT_META_TTL_MS)) {
    return cachedEventCampaignMeta;
  }
  const fallback = {
    bfPrefix: 'byo-bf-v10-',
    lnPrefix: 'byo-ln-v5-',
    bfBoundaries: [],
    lnBoundaries: []
  };
  try {
    const [bfRes, lnRes] = await Promise.all([
      fetch('https://events.swiggy.com/book-your-offer?utm_source=app&utm_medium=share', { signal: AbortSignal.timeout(5000) }),
      fetch('https://events.swiggy.com/pick-your-late-night-offer?utm_source=app&utm_medium=share', { signal: AbortSignal.timeout(5000) })
    ]);
    const [bfHtml, lnHtml] = await Promise.all([bfRes.text(), lnRes.text()]);
    const parseNexus = (html, defPrefix) => {
      const m = html.match(/<script id="__NEXT_DATA__"[^>]*>([\s\S]*?)<\/script>/);
      if (!m) return { prefix: defPrefix, boundaries: [] };
      try {
        const parsed = JSON.parse(m[1]);
        const nexus = parsed?.props?.pageProps?.nexusData || {};
        return {
          prefix: nexus.notifyCampaignIdPrefix || defPrefix,
          boundaries: Array.isArray(nexus.dayBoundaries) ? nexus.dayBoundaries : []
        };
      } catch {
        return { prefix: defPrefix, boundaries: [] };
      }
    };
    const bf = parseNexus(bfHtml, 'byo-bf-v10-');
    const ln = parseNexus(lnHtml, 'byo-ln-v5-');
    cachedEventCampaignMeta = {
      bfPrefix: bf.prefix,
      lnPrefix: ln.prefix,
      bfBoundaries: bf.boundaries,
      lnBoundaries: ln.boundaries
    };
    cachedEventCampaignMetaAt = Date.now();
    return cachedEventCampaignMeta;
  } catch (e) {
    console.warn('[EventsClaim] Dynamic campaign lookup fallback used:', e.message);
    return cachedEventCampaignMeta || fallback;
  }
}

function resolveCampaignWindowInfo(boundaries, prefix, defaultDay = 15, isLateNight = false, nowMs = Date.now()) {
  let matched = null;
  for (const d of (boundaries || [])) {
    const start = Date.parse(d.startTime);
    const end = Date.parse(d.endTime);
    if (nowMs >= start && nowMs < end) {
      matched = { ...d, startMs: start, endMs: end };
      break;
    }
  }
  if (!matched && Array.isArray(boundaries) && boundaries.length > 0) {
    const start1 = Date.parse(boundaries[0].startTime);
    const diff = Math.floor((nowMs - start1) / (24 * 3600 * 1000)) + 1;
    const clampedIdx = Math.max(0, Math.min(diff - 1, boundaries.length - 1));
    const b = boundaries[clampedIdx];
    matched = { ...b, startMs: Date.parse(b.startTime), endMs: Date.parse(b.endTime) };
  }
  const currentDay = matched?.day || defaultDay;
  const maxDay = (boundaries && boundaries.length > 0)
    ? Math.max(...boundaries.map(b => Number(b.day) || 0), currentDay + 14)
    : currentDay + 14;

  // Exact Swiggy cutoff timestamps from `pick-your-late-night-offer` module 17858 (`day` starts 11:00 IST):
  // - Late Night: voting closes at 18:30 IST (+7.5h from 11:00 startTime), active redeem slot 21:00–06:00 IST (+10h..+19h)
  // - Breakfast: voting closes at 05:00 IST (+18h from 11:00 startTime), active redeem slot 07:00–11:00 IST (+20h..+24h)
  let cutoffMs = null;
  let slotOpenMs = null;
  if (matched?.startMs) {
    cutoffMs = matched.startMs + (isLateNight ? 7.5 * 3600 * 1000 : 18 * 3600 * 1000);
    slotOpenMs = matched.startMs + (isLateNight ? 10 * 3600 * 1000 : 20 * 3600 * 1000);
  }

  return {
    currentDay,
    maxDay,
    todayCampaign: `${prefix}${currentDay}`,
    upcomingDays: Array.from(
      { length: Math.min(2, Math.max(1, maxDay - currentDay + 1)) },
      (_, idx) => `${prefix}${currentDay + idx}`
    ),
    cutoffMs,
    slotOpenMs,
    endMs: matched?.endMs || null
  };
}

export async function claimSwiggyBreakfastAndLateNightOffers(account, { force = false, offerValue = null, forcePatch = false, quickLockOnly = false } = {}) {
  if (!account) return { success: false, reason: 'No account provided' };
  const chosenVal = [1, 2, 3, 4].includes(Number(offerValue || account.preferredOfferValue))
    ? Number(offerValue || account.preferredOfferValue)
    : 1;
  const chosenMeta = EVENT_OFFER_OPTIONS[chosenVal] || EVENT_OFFER_OPTIONS[1];
  const accSig = `${String(account.id || account.phone || account.customerId || account.token || (account.cookies || '').slice(0, 60))}:v${chosenVal}`;
  if (!force && !forcePatch && accSig && offerClaimCache.has(accSig)) {
    const prev = offerClaimCache.get(accSig);
    if (Date.now() - prev.ts < OFFER_CLAIM_TTL_MS) return prev.result;
  }

  let token = account.token || '';
  let jwtTid = account.tid || '';
  let cookieStr = stripStaleWafCookie(account.cookies || '');

  if (cookieStr) {
    const tidCookie = cookieStr.split(';').map(s => s.trim()).find(s => s.startsWith('tid='));
    if (tidCookie && tidCookie.slice(4).includes('.')) {
      jwtTid = tidCookie.slice(4);
    }
    if (!token) {
      const tokCookie = cookieStr.split(';').map(s => s.trim()).find(s => s.startsWith('token='));
      if (tokCookie) {
        token = tokCookie.slice(6);
      }
    }
  }

  // Refresh live 30-day `jwtTid` via zero-WAF Android `chkout` first (fast ~180ms), fallback to `/dapi/order/all`!
  let liveSessionDead = false;
  const nowSec = Math.floor(Date.now() / 1000);
  if ((!jwtTid || decodeJwtExpSec(jwtTid) < nowSec + 120) && (token || jwtTid || cookieStr)) {
    try {
      const chkRes = await fetch('https://chkout.swiggy.com/api/v2/cart/client', {
        headers: {
          'User-Agent': 'Swiggy-Android',
          'app-version': '4.67.0',
          'version-code': '1365',
          'os-version': '13',
          'Accept': 'application/json',
          ...(jwtTid ? { tid: jwtTid } : {}),
          ...(token ? { token } : {}),
          ...(account.sid ? { sid: account.sid } : {}),
          ...(account.deviceId ? { deviceId: account.deviceId, swuid: account.deviceId } : {})
        },
        signal: AbortSignal.timeout(5000)
      });
      const chkJson = await chkRes.json().catch(() => null);
      if (chkJson?.statusCode === 0 && chkJson?.tid && String(chkJson.tid).includes('.')) {
        jwtTid = chkJson.tid;
        account.jwtTid = jwtTid;
        if (!account.tid || String(account.tid).includes('.')) account.tid = jwtTid;
      } else if (chkJson?.statusCode === 999) {
        liveSessionDead = true;
      }
    } catch {}
  }

  if ((!jwtTid || decodeJwtExpSec(jwtTid) < nowSec + 120) && cookieStr) {
    try {
      const authRes = await fetch('https://www.swiggy.com/dapi/order/all', {
        headers: {
          'Cookie': cookieStr,
          'User-Agent': 'Swiggy-Android',
          'Accept': 'application/json',
          'Referer': 'https://www.swiggy.com/my-account'
        },
        signal: AbortSignal.timeout(5000)
      });
      const authJson = await authRes.json().catch(() => null);
      if (authRes.status === 200 && authJson?.statusCode === 0 && authJson?.tid) {
        jwtTid = authJson.tid;
        account.jwtTid = jwtTid;
        if (!account.tid || String(account.tid).includes('.')) account.tid = jwtTid;
        const setCookies = typeof authRes.headers.getSetCookie === 'function' ? authRes.headers.getSetCookie() : [];
        if (setCookies.length > 0) {
          cookieStr = mergeSetCookiesIntoJar(cookieStr, setCookies);
        }
      } else if (authJson?.statusCode === 1) {
        liveSessionDead = true;
      }
    } catch {}
  }

  if (!token && jwtTid) {
    token = jwtTid;
  }

  if (!jwtTid && !token) {
    return { success: false, sessionExpired: true, reason: 'Session Logged Out — Re-login required' };
  }

  if (!cookieStr && jwtTid) {
    cookieStr = `tid=${jwtTid}` + (account.sid ? `; _sid=${account.sid}` : '') + (account.deviceId ? `; _device_id=${account.deviceId}` : '');
  }

  const nowMs = Date.now();
  const meta = await getLiveEventCampaignMeta(false);
  const bfWin = resolveCampaignWindowInfo(meta.bfBoundaries, meta.bfPrefix, 15, false, nowMs);
  const lnWin = resolveCampaignWindowInfo(meta.lnBoundaries, meta.lnPrefix, 15, true, nowMs);

  // CRITICAL: `events.swiggy.com/api/notify` authenticates strictly via `{ token, tid }` headers!
  // Sending `Cookie:` triggers CloudFront WAF `403 Forbidden` on accounts with multi-domain web cookies!
  const baseHeaders = {
    'Content-Type': 'application/json',
    'Accept': 'application/json',
    'token': token || jwtTid,
    'tid': jwtTid,
    'Origin': 'https://events.swiggy.com',
    'User-Agent': 'Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Mobile Safari/537.36'
  };

  try {
    // CloudFront WAF-safe (`<40 req/10s/IP`) 48-Hour Rolling Pre-Book (`Today + Tomorrow` = `4` campaigns total!):
    // 1) `GET /api/notify?campaign=<id>` checks real live state (`shouldNotify`, `value`, `timestamp`).
    // 2) If already `shouldNotify === true` AND `Number(value) === chosenVal` -> `0` extra mutations needed!
    // 3) If unsubscribed -> single `POST`; if subscribed with a different `value` -> single `PATCH` (never redundant `POST + PATCH`)!
    // 4) If CloudFront burst limit (`403`/`429`) triggers, waits `5.5s` for window reset and retries cleanly!
    const prevLockedMap = (account.offers && typeof account.offers.lockedMap === 'object' && account.offers.lockedMap)
      ? { ...account.offers.lockedMap }
      : {};

    const syncSingleCampaign = async (campaignId, referer) => {
      for (let tryIdx = 0; tryIdx < 2; tryIdx++) {
        if (tryIdx > 0) await new Promise(r => setTimeout(r, 5500));

        const statusRes = await fetch(`https://events.swiggy.com/api/notify?campaign=${encodeURIComponent(campaignId)}`, {
          headers: baseHeaders,
          signal: AbortSignal.timeout(5500)
        });
        if ((statusRes.status === 403 || statusRes.status === 429) && tryIdx === 0) continue;
        const statusJson = await statusRes.json().catch(() => ({}));

        const isSubscribed = Boolean(statusJson?.shouldNotify);
        const curVal = Number(statusJson?.value || 0);

        // Already locked on Swiggy's server with the exact desired reward value!
        if (statusRes.ok && isSubscribed && curVal === chosenVal) {
          prevLockedMap[campaignId] = chosenVal;
          return { res: statusRes, json: { ...statusJson, message: 'Already active' }, statusJson };
        }

        // Need either `POST` (first time subscribing) or `PATCH` (switching reward option 1..4)!
        const writeMethod = isSubscribed ? 'PATCH' : 'POST';
        const writeRes = await fetch('https://events.swiggy.com/api/notify', {
          method: writeMethod,
          headers: { ...baseHeaders, 'Referer': referer },
          body: JSON.stringify({ campaign: campaignId, value: chosenVal }),
          signal: AbortSignal.timeout(6500)
        });
        if ((writeRes.status === 403 || writeRes.status === 429) && tryIdx === 0) continue;
        const writeJson = await writeRes.json().catch(() => ({}));

        // If `POST` says already subscribed with a different value, do a single `PATCH` to update `value`:
        const alreadyMsg = String(writeJson?.message || '').toLowerCase().includes('already');
        if (writeMethod === 'POST' && alreadyMsg && Number(writeJson?.value || 0) !== chosenVal) {
          const patchRes = await fetch('https://events.swiggy.com/api/notify', {
            method: 'PATCH',
            headers: { ...baseHeaders, 'Referer': referer },
            body: JSON.stringify({ campaign: campaignId, value: chosenVal }),
            signal: AbortSignal.timeout(6500)
          });
          if ((patchRes.status === 403 || patchRes.status === 429) && tryIdx === 0) continue;
          const patchJson = await patchRes.json().catch(() => ({}));
          if (patchRes.ok) prevLockedMap[campaignId] = chosenVal;
          return { res: patchRes, json: patchJson, statusJson: { ...statusJson, shouldNotify: true, value: chosenVal } };
        }

        if (writeRes.ok || alreadyMsg) {
          prevLockedMap[campaignId] = chosenVal;
        }
        return {
          res: writeRes,
          json: writeJson,
          statusJson: {
            ...statusJson,
            shouldNotify: Boolean(writeRes.ok || alreadyMsg || isSubscribed),
            value: chosenVal,
            timestamp: statusJson?.timestamp || writeJson?.currentTime || new Date().toISOString()
          }
        };
      }
      return { res: { ok: false, status: 403, statusText: 'Rate Limited' }, json: {}, statusJson: {} };
    };

    const maxLen = Math.max(bfWin.upcomingDays.length, lnWin.upcomingDays.length);
    const immediateLen = quickLockOnly ? Math.min(2, maxLen) : maxLen;
    const bfSlots = new Array(immediateLen).fill(null);
    const lnSlots = new Array(immediateLen).fill(null);

    const BATCH_CONCURRENCY = 5;
    for (let start = 0; start < immediateLen; start += BATCH_CONCURRENCY) {
      const indices = [];
      for (let idx = start; idx < Math.min(immediateLen, start + BATCH_CONCURRENCY); idx++) {
        indices.push(idx);
      }
      await Promise.all(indices.map(async (i) => {
        const [bItem, lItem] = await Promise.all([
          bfWin.upcomingDays[i]
            ? syncSingleCampaign(bfWin.upcomingDays[i], 'https://events.swiggy.com/book-your-offer')
            : Promise.resolve(null),
          lnWin.upcomingDays[i]
            ? syncSingleCampaign(lnWin.upcomingDays[i], 'https://events.swiggy.com/pick-your-late-night-offer')
            : Promise.resolve(null)
        ]);
        bfSlots[i] = bItem;
        lnSlots[i] = lItem;
      }));
    }

    const bfAll = bfSlots.filter(Boolean);
    const lnAll = lnSlots.filter(Boolean);

    // If `quickLockOnly` locked Today + Tomorrow for sub-second login latency, finish pre-locking days 2..14 in background!
    if (quickLockOnly && maxLen > immediateLen && (bfAll[0]?.res?.ok || lnAll[0]?.res?.ok)) {
      Promise.resolve().then(async () => {
        for (let start = immediateLen; start < maxLen; start += BATCH_CONCURRENCY) {
          const indices = [];
          for (let idx = start; idx < Math.min(maxLen, start + BATCH_CONCURRENCY); idx++) indices.push(idx);
          await Promise.allSettled(indices.map((i) => Promise.all([
            bfWin.upcomingDays[i]
              ? syncSingleCampaign(bfWin.upcomingDays[i], 'https://events.swiggy.com/book-your-offer')
              : Promise.resolve(null),
            lnWin.upcomingDays[i]
              ? syncSingleCampaign(lnWin.upcomingDays[i], 'https://events.swiggy.com/pick-your-late-night-offer')
              : Promise.resolve(null)
          ])));
        }
      }).catch(() => {});
    }

    if (!bfAll.length) bfAll.push({ res: { ok: false, status: 500, statusText: 'Empty' }, json: {}, statusJson: {} });
    if (!lnAll.length) lnAll.push({ res: { ok: false, status: 500, statusText: 'Empty' }, json: {}, statusJson: {} });

    const bfStatusNow = bfAll[0]?.statusJson || {};
    const lnStatusNow = lnAll[0]?.statusJson || {};

    const { res: resBf, json: bfJson } = bfAll[0];
    const { res: resLn, json: lnJson } = lnAll[0];

    const bfLockedCount = bfAll.filter(x => x.res.ok || String(x.json?.message || '').toLowerCase().includes('already')).length;
    const lnLockedCount = lnAll.filter(x => x.res.ok || String(x.json?.message || '').toLowerCase().includes('already')).length;

    const bfOk = bfLockedCount > 0;
    const lnOk = lnLockedCount > 0;

    const describeSlotState = (ok, res, json, statusNow, win, isLn) => {
      if (!ok) {
        if (res.status === 401 || liveSessionDead) return { state: 'EXPIRED', msg: 'Session Expired — Re-login required' };
        if (res.status === 403) return { state: 'FORBIDDEN', msg: 'HTTP 403 Forbidden (WAF Blocked)' };
        return { state: 'FAILED', msg: `HTTP ${res.status} (${json.message || res.statusText || 'Error'})` };
      }
      const bookedAtMs = statusNow?.timestamp ? Date.parse(statusNow.timestamp) : nowMs;
      const bookedBeforeCutoff = !win.cutoffMs || bookedAtMs <= win.cutoffMs;
      const inRedeemSlotNow = Boolean(win.slotOpenMs && win.endMs && nowMs >= win.slotOpenMs && nowMs < win.endMs);
      const valTag = (EVENT_OFFER_OPTIONS[statusNow?.value || chosenVal] || chosenMeta).shortLabel;
      const daysTag = `+${Math.max(0, (isLn ? lnLockedCount : bfLockedCount) - 1)} next days pre-locked`;

      if (bookedBeforeCutoff && inRedeemSlotNow) {
        return { state: 'ACTIVE_NOW', msg: `● LIVE IN CART NOW (${valTag} • ${daysTag})` };
      }
      if (bookedBeforeCutoff) {
        return {
          state: 'LOCKED_FOR_TODAY',
          msg: `✓ Booked Before Cutoff (${valTag} • activates ${isLn ? '9:00 PM' : '7:00 AM'} • ${daysTag})`
        };
      }
      return {
        state: 'CUTOFF_PASSED_LOCKED_NEXT_14D',
        msg: `◷ Today's ${isLn ? '6:30 PM' : '5:00 AM'} cutoff passed before login — Next 14 Days PRE-LOCKED (${valTag})!`
      };
    };

    const bfDesc = describeSlotState(bfOk, resBf, bfJson, bfStatusNow, bfWin, false);
    const lnDesc = describeSlotState(lnOk, resLn, lnJson, lnStatusNow, lnWin, true);

    console.log(`[EventsClaim] Account ${account.phone || account.name || 'User'} result:`, {
      offerValue: chosenVal,
      breakfast: { campaign: bfWin.todayCampaign, lockedDays: bfLockedCount, state: bfDesc.state },
      lateNight: { campaign: lnWin.todayCampaign, lockedDays: lnLockedCount, state: lnDesc.state }
    });

    const claimOut = {
      success: bfOk || lnOk,
      bothClaimed: bfOk && lnOk,
      offerValue: chosenVal,
      offerLabel: chosenMeta.shortLabel,
      lockedMap: prevLockedMap,
      sessionExpired: !bfOk && !lnOk && (resBf.status === 401 || resLn.status === 401 || liveSessionDead),
      breakfast: {
        name: 'Breakfast Morning (7AM–11AM)',
        campaign: bfWin.todayCampaign,
        lockedDaysCount: bfLockedCount,
        upcomingCampaigns: bfWin.upcomingDays,
        slotState: bfDesc.state,
        status: bfOk ? 'CLAIMED' : 'FAILED',
        statusCode: resBf.status,
        discount: chosenMeta.shortLabel,
        offerValue: Number(bfStatusNow?.value || chosenVal),
        rawMessage: bfJson.message || '',
        message: bfDesc.msg
      },
      lateNight: {
        name: 'Late Night (9PM–6AM)',
        campaign: lnWin.todayCampaign,
        lockedDaysCount: lnLockedCount,
        upcomingCampaigns: lnWin.upcomingDays,
        slotState: lnDesc.state,
        status: lnOk ? 'CLAIMED' : 'FAILED',
        statusCode: resLn.status,
        discount: chosenMeta.shortLabel,
        offerValue: Number(lnStatusNow?.value || chosenVal),
        rawMessage: lnJson.message || '',
        message: lnDesc.msg
      }
    };
    if (accSig) offerClaimCache.set(accSig, { result: claimOut, ts: Date.now() });
    return claimOut;
  } catch (err) {
    console.error('[EventsClaim] Request error:', err.message);
    return { success: false, error: err.message };
  }
}

async function launchStealthSwiggyBrowser() {
  const browser = await puppeteer.launch({
    executablePath: CHROME_PATH,
    headless: HEADLESS_MODE,
    protocolTimeout: 60000,
    ignoreDefaultArgs: ['--enable-automation'],
    args: [
      '--disable-blink-features=AutomationControlled',
      '--no-sandbox',
      '--disable-setuid-sandbox',
      '--disable-gpu',
      '--disable-dev-shm-usage',
      '--no-first-run',
      '--no-default-browser-check',
      '--disable-background-timer-throttling',
      '--disable-backgrounding-occluded-windows',
      '--disable-renderer-backgrounding',
      '--window-size=1366,768',
      '--lang=en-IN,en-US,en'
    ]
  });

  const page = await browser.newPage();
  const cleanSyntheticEntityId = crypto.randomUUID();
  await page.setViewport({ width: 1366, height: 768 });
  await page.emulateTimezone('Asia/Kolkata').catch(() => {});
  await page.setUserAgent('Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36');

  // Intercept `fna.swiggy.com/api/fraudnabuse/*` so Headless Linux container never flags newly logged-in accounts into Promo-Restricted segment!
  await page.setRequestInterception(true);
  page.on('request', (req) => {
    const u = req.url();
    if (u.includes('fna.swiggy.com/api/fraudnabuse')) {
      return req.respond({
        status: 200,
        contentType: 'application/json',
        headers: {
          'Access-Control-Allow-Origin': 'https://www.swiggy.com',
          'Access-Control-Allow-Credentials': 'true',
          'Access-Control-Allow-Headers': 'Content-Type, Accept'
        },
        body: JSON.stringify({ statusCode: 0, statusMessage: 'success', data: cleanSyntheticEntityId, successful: true })
      }).catch(() => {});
    }
    req.continue().catch(() => {});
  });

  await page.evaluateOnNewDocument(() => {
    try {
      delete Object.getPrototypeOf(navigator).webdriver;
    } catch (e) {}
    Object.defineProperty(navigator, 'webdriver', { get: () => undefined, configurable: true });
    Object.defineProperty(navigator, 'platform', { get: () => 'Win32' });
    Object.defineProperty(navigator, 'hardwareConcurrency', { get: () => 8 });
    Object.defineProperty(navigator, 'deviceMemory', { get: () => 8 });
    if (!window.chrome) window.chrome = {};
    window.chrome.runtime = window.chrome.runtime || { connect: () => {}, sendMessage: () => {} };
    window.chrome.loadTimes = window.chrome.loadTimes || (() => ({}));
    window.chrome.csi = window.chrome.csi || (() => ({}));
    window.chrome.app = window.chrome.app || {};
    Object.defineProperty(navigator, 'languages', { get: () => ['en-IN', 'en-US', 'en'] });
    if (!navigator.plugins || navigator.plugins.length === 0) {
      Object.defineProperty(navigator, 'plugins', {
        get: () => [
          { name: 'Chrome PDF Plugin', filename: 'internal-pdf-viewer', description: 'Portable Document Format' },
          { name: 'Chrome PDF Viewer', filename: 'mhjfbmdgcfjbbpaeojofohoefgiehjai', description: '' }
        ]
      });
    }
  });
  return { browser, page };
}

function canUseStealthBrowser() {
  try {
    return Boolean(CHROME_PATH && fs.existsSync(CHROME_PATH));
  } catch {
    return false;
  }
}

const MOBILE_DEVICE_PROFILES = [
  {
    ua: 'Mozilla/5.0 (Linux; Android 14; Pixel 7 Build/AP2A.240805.005) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.6778.135 Mobile Safari/537.36',
    secChUa: '"Google Chrome";v="131", "Chromium";v="131", "Not_A Brand";v="24"',
    model: 'Pixel 7',
    osVersion: '14'
  },
  {
    ua: 'Mozilla/5.0 (Linux; Android 14; SM-S911B Build/UP1A.231005.007) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.6778.135 Mobile Safari/537.36',
    secChUa: '"Google Chrome";v="131", "Chromium";v="131", "Not_A Brand";v="24"',
    model: 'SM-S911B',
    osVersion: '14'
  },
  {
    ua: 'Mozilla/5.0 (Linux; Android 13; CPH2447 Build/TP1A.220905.001) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.6778.135 Mobile Safari/537.36',
    secChUa: '"Google Chrome";v="131", "Chromium";v="131", "Not_A Brand";v="24"',
    model: 'CPH2447',
    osVersion: '13'
  },
  {
    ua: 'Mozilla/5.0 (Linux; Android 14; 23127PN0CG Build/UKQ1.230804.001) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.6778.135 Mobile Safari/537.36',
    secChUa: '"Google Chrome";v="131", "Chromium";v="131", "Not_A Brand";v="24"',
    model: '23127PN0CG',
    osVersion: '14'
  }
];

function buildAntiBotDeviceProfile(phone = '') {
  const daySalt = new Date().toISOString().slice(0, 10);
  const hashHex = crypto.createHash('sha256').update(`swiggy-auth-dev:${phone}:${daySalt}`).digest('hex');
  // Deterministic RFC-4122 UUIDv4 per (phone, day) so Swiggy FNA sees one consistent device across OTP -> Verify -> Signup
  const deviceId = [
    hashHex.slice(0, 8),
    hashHex.slice(8, 12),
    `4${hashHex.slice(13, 16)}`,
    `${['8', '9', 'a', 'b'][parseInt(hashHex[16], 16) % 4]}${hashHex.slice(17, 20)}`,
    hashHex.slice(20, 32)
  ].join('-');
  const idx = parseInt(hashHex.slice(32, 36), 16) % MOBILE_DEVICE_PROFILES.length;
  const profile = MOBILE_DEVICE_PROFILES[idx];
  return {
    deviceId,
    swuid: deviceId,
    ...profile
  };
}

function getResponseSetCookies(res) {
  if (!res || !res.headers) return [];
  if (typeof res.headers.getSetCookie === 'function') {
    const arr = res.headers.getSetCookie();
    if (Array.isArray(arr) && arr.length > 0) return arr;
  }
  const single = typeof res.headers.get === 'function' ? res.headers.get('set-cookie') : '';
  if (!single) return [];
  return String(single).split(/,(?=\s*[!#$%&'*+\-.^_`|~0-9A-Za-z]+=)/g).map(s => s.trim()).filter(Boolean);
}

function applySetCookiesToMap(cookieMap, setCookieHeaders = []) {
  for (const raw of (setCookieHeaders || [])) {
    const parts = String(raw || '').split(';').map(s => s.trim()).filter(Boolean);
    if (!parts.length) continue;
    const eqIdx = parts[0].indexOf('=');
    if (eqIdx <= 0) continue;
    const name = parts[0].slice(0, eqIdx).trim();
    const val = parts[0].slice(eqIdx + 1).trim();
    if (!name || name === 'aws-waf-token') continue;

    const attrsLower = parts.slice(1).join('; ').toLowerCase();
    const expired = /max-age\s*=\s*0\b/.test(attrsLower) || val === '' || val === 'deleted';
    if (expired) {
      cookieMap.delete(name);
    } else {
      cookieMap.set(name, val);
    }
  }
}

function serializeCookieMap(cookieMap) {
  return Array.from(cookieMap.entries())
    .filter(([k, v]) => k && v !== undefined && v !== null && v !== '')
    .map(([k, v]) => `${k}=${v}`)
    .join('; ');
}

function createSwiggyHttpAuthSession(phone, targetAcc = '', targetAccName = null) {
  const deviceProfile = buildAntiBotDeviceProfile(phone);
  const cookieMap = new Map();
  cookieMap.set('_device_id', deviceProfile.deviceId);
  cookieMap.set('swuid', deviceProfile.swuid);
  cookieMap.set('_is_logged_in', '0');
  cookieMap.set('userLocation', encodeURIComponent(JSON.stringify({
    lat: '26.8467',
    lng: '80.9462',
    address: 'Lucknow, Uttar Pradesh, India',
    area: 'Lucknow',
    id: ''
  })));
  return {
    mode: 'http',
    phone,
    otp: null,
    targetAcc: targetAcc || `acc_${phone}`,
    targetAccName: targetAccName || null,
    deviceProfile,
    cookieMap,
    csrfToken: '',
    transportMode: 'mweb',
    isNewUser: false,
    signupPreRegistered: false,
    signupName: '',
    signupEmail: '',
    browser: null,
    page: null,
    safetyTimer: null,
    createdAt: Date.now()
  };
}

function buildAuthRequestHeaders(session, { referer = 'https://www.swiggy.com/auth', useAndroidUa = false, extra = {} } = {}) {
  const cookieHeader = serializeCookieMap(session.cookieMap);
  const dev = session.deviceProfile || buildAntiBotDeviceProfile(session.phone || '');
  if (useAndroidUa || session.transportMode === 'android') {
    const sidVal = session.cookieMap.get('_sid') || '';
    const tidVal = session.cookieMap.get('tid') || session.cookieMap.get('_guest_tid') || '';
    return {
      ...(cookieHeader ? { 'Cookie': cookieHeader } : {}),
      'User-Agent': 'Swiggy-Android',
      'Accept': 'application/json, text/plain, */*',
      'Content-Type': 'application/json',
      'Accept-Language': 'en-IN,en-GB;q=0.9,en-US;q=0.8',
      'Origin': 'https://www.swiggy.com',
      'Referer': referer,
      'app-version': '4.67.0',
      'version-code': '1365',
      'os-version': dev.osVersion || '14',
      'deviceId': dev.deviceId,
      'swuid': dev.swuid,
      ...(sidVal ? { 'sid': sidVal } : {}),
      ...(tidVal ? { 'tid': tidVal } : {}),
      ...extra
    };
  }

  return {
    ...(cookieHeader ? { 'Cookie': cookieHeader } : {}),
    'User-Agent': dev.ua,
    'Accept': 'application/json, text/plain, */*',
    'Content-Type': 'application/json',
    'Accept-Language': 'en-IN,en-GB;q=0.9,en-US;q=0.8,hi;q=0.7',
    'Origin': 'https://www.swiggy.com',
    'Referer': referer,
    '__fetch_req__': 'true',
    'platform': 'mweb',
    'Sec-Ch-Ua': dev.secChUa,
    'Sec-Ch-Ua-Mobile': '?1',
    'Sec-Ch-Ua-Platform': '"Android"',
    'Sec-Fetch-Dest': 'empty',
    'Sec-Fetch-Mode': 'cors',
    'Sec-Fetch-Site': 'same-origin',
    ...extra
  };
}

function isAwsWafChallengeResponse(status, rawText = '', headers = null) {
  const wafHeader = headers && typeof headers.get === 'function' ? (headers.get('x-amzn-waf-action') || '') : '';
  if (wafHeader) return true;
  if (Number(status) === 202) return true;
  const lower = String(rawText || '').toLowerCase();
  if (Number(status) === 403 && /awswaf|captcha|challenge|verify you are human|bot verification|automated traffic|cloudfront/.test(lower)) {
    return true;
  }
  if (/awswafintegration|gokuprops|x-amzn-waf/.test(lower)) return true;
  return false;
}

function isCsrfMismatchResponse(status, rawText = '', data = null) {
  if (Number(status) !== 403 && Number(status) !== 400) return false;
  const combined = `${rawText || ''} ${data?.statusMessage || ''} ${data?.message || ''}`.toLowerCase();
  return /csrf|invalid token|forbidden/.test(combined) && !isAwsWafChallengeResponse(status, rawText);
}

// Fast (~200-350ms, 0MB RAM, zero-Chromium) Swiggy `_csrf` + `_guest_tid` + `_sid` bootstrap!
async function bootstrapSwiggyAuthJar(session, { forceFresh = false } = {}) {
  if (!forceFresh && session.csrfToken && (session.cookieMap.has('_csrf') || session.cookieMap.has('_sid') || session.cookieMap.has('_guest_tid'))) {
    return session.csrfToken;
  }
  if (forceFresh) {
    session.csrfToken = '';
    session.cookieMap.delete('_csrf');
  }

  // Probe 1: Fast WebView HTML route `/web-cart-add-address` (sets `_csrf` cookie + embeds `window._csrf` with zero WAF)
  try {
    const dev = session.deviceProfile || buildAntiBotDeviceProfile(session.phone || '');
    const res = await fetch('https://www.swiggy.com/web-cart-add-address', {
      method: 'GET',
      headers: {
        'Cookie': serializeCookieMap(session.cookieMap),
        'User-Agent': dev.ua,
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
        'Accept-Language': 'en-IN,en-GB;q=0.9,en-US;q=0.8',
        'X-Requested-With': 'in.swiggy.android'
      },
      redirect: 'manual',
      signal: AbortSignal.timeout(3500)
    });
    applySetCookiesToMap(session.cookieMap, getResponseSetCookies(res));
    const html = await res.text().catch(() => '');
    let parsedJson = null;
    try { parsedJson = JSON.parse(html); } catch {}
    const csrfMatch = html.match(/window\._csrf\s*=\s*["']([^"']+)["']/) || html.match(/csrfToken["']?\s*:\s*["']([^"']+)["']/);
    const extracted = (csrfMatch && csrfMatch[1]) || parsedJson?.csrfToken || '';
    if (extracted) {
      session.csrfToken = extracted;
      return session.csrfToken;
    }
  } catch {}

  // Probe 2: Zero-WAF DAPI JSON `/dapi/order/all` or `/dapi/cart` with `Swiggy-Android` UA
  for (const probeUrl of ['https://www.swiggy.com/dapi/order/all', 'https://www.swiggy.com/dapi/cart']) {
    try {
      const res = await fetch(probeUrl, {
        method: 'GET',
        headers: buildAuthRequestHeaders(session, { referer: 'https://www.swiggy.com/', useAndroidUa: true }),
        signal: AbortSignal.timeout(3500)
      });
      applySetCookiesToMap(session.cookieMap, getResponseSetCookies(res));
      const text = await res.text().catch(() => '');
      let json = null;
      try { json = JSON.parse(text); } catch {}
      if (json?.tid && !session.cookieMap.has('_guest_tid') && !session.cookieMap.has('tid')) {
        session.cookieMap.set('_guest_tid', String(json.tid));
      }
      if (json?.sid && !session.cookieMap.has('_sid')) {
        session.cookieMap.set('_sid', String(json.sid));
      }
      if (json?.csrfToken) {
        session.csrfToken = String(json.csrfToken);
        return session.csrfToken;
      }
    } catch {}
  }

  if (!session.csrfToken && session.cookieMap.get('_csrf')) {
    session.csrfToken = session.cookieMap.get('_csrf');
  }
  return session.csrfToken;
}

async function postSwiggyAuthJson(session, endpointUrl, payload = {}, { timeoutMs = 6500, allowBrowserEscalation = true } = {}) {
  await bootstrapSwiggyAuthJar(session);

  const sendOnce = async (useAndroidUa = false) => {
    const bodyObj = { ...payload };
    if (session.csrfToken && bodyObj._csrf === undefined) {
      bodyObj._csrf = session.csrfToken;
    }
    const res = await fetch(endpointUrl, {
      method: 'POST',
      headers: buildAuthRequestHeaders(session, { referer: 'https://www.swiggy.com/auth', useAndroidUa }),
      body: JSON.stringify(bodyObj),
      signal: AbortSignal.timeout(timeoutMs)
    });
    applySetCookiesToMap(session.cookieMap, getResponseSetCookies(res));
    const rawText = await res.text().catch(() => '');
    let data = {};
    try { data = JSON.parse(rawText); } catch {}
    if (data?.csrfToken) session.csrfToken = String(data.csrfToken);
    if (data?.tid && !session.cookieMap.has('_session_tid')) {
      session.cookieMap.set('tid', String(data.tid));
    }
    if (data?.sid) {
      session.cookieMap.set('_sid', String(data.sid));
    }
    return { status: res.status, data, rawText, headers: res.headers };
  };

  let out = await sendOnce(session.transportMode === 'android');

  // Auto-recover 1: Stale or missing CSRF token (HTTP 403/400 `invalid csrf token`, NOT AWS WAF!)
  if (isCsrfMismatchResponse(out.status, out.rawText, out.data)) {
    await bootstrapSwiggyAuthJar(session, { forceFresh: true });
    out = await sendOnce(session.transportMode === 'android');
  }

  // Auto-recover 2: If mWeb transport hit an AWS WAF challenge, retry once over `Swiggy-Android` transport!
  if (isAwsWafChallengeResponse(out.status, out.rawText, out.headers) && session.transportMode !== 'android') {
    session.transportMode = 'android';
    await bootstrapSwiggyAuthJar(session, { forceFresh: true });
    out = await sendOnce(true);
  }

  // Auto-recover 3: Optional Stealth Browser escalation ONLY if still WAF-challenged AND local Chromium exists!
  if (allowBrowserEscalation && isAwsWafChallengeResponse(out.status, out.rawText, out.headers) && canUseStealthBrowser()) {
    try {
      if (!session.page || !session.browser?.connected) {
        const launched = await launchStealthSwiggyBrowser();
        session.browser = launched.browser;
        session.page = launched.page;
        session.mode = 'browser';
        await session.page.goto('https://www.swiggy.com/auth', { waitUntil: 'domcontentloaded', timeout: 10000 }).catch(() => {});
        await waitForSwiggyWafCookie(session.page, 2500);
      }
      const pageCookies = await session.page.cookies().catch(() => []);
      const wafToken = pageCookies.find(c => c.name === 'aws-waf-token')?.value || '';
      const relPath = endpointUrl.replace(/^https?:\/\/www\.swiggy\.com/i, '');
      const browserOut = await safeEvaluateAuthOnce(session.page, async (targetPath, bodyInput, waf) => {
        try {
          const csrf = (typeof window !== 'undefined' && window._csrf) ? window._csrf : '';
          const headers = { 'Content-Type': 'application/json', 'Accept': 'application/json' };
          if (waf) headers['aws-waf-token'] = waf;
          const finalPayload = { ...bodyInput, ...(csrf && bodyInput._csrf === undefined ? { _csrf: csrf } : {}) };
          const r = await fetch(targetPath, {
            method: 'POST',
            headers,
            body: JSON.stringify(finalPayload),
            credentials: 'include',
            signal: AbortSignal.timeout(7500)
          });
          const txt = await r.text().catch(() => '');
          let j = {};
          try { j = JSON.parse(txt); } catch {}
          return { status: r.status, data: j, rawText: txt };
        } catch (e) {
          return { status: 500, error: e.message };
        }
      }, relPath, payload, wafToken);
      const afterCookies = await session.page.cookies().catch(() => []);
      for (const c of afterCookies) {
        if (c?.name && c?.value && c.name !== 'aws-waf-token') session.cookieMap.set(c.name, c.value);
      }
      return browserOut;
    } catch {}
  }

  return out;
}

function isUnregisteredSwiggyAuthResponse(result) {
  if (!result || (result.status !== 200 && result.status !== 202)) return false;
  const msgLower = `${result.data?.statusMessage || ''} ${result.data?.message || ''} ${result.rawText || ''}`.toLowerCase();
  if (/rate limit|too many|limit reached|maximum|valid 10 digit|invalid otp|incorrect otp|wrong otp|expired otp|something went wrong|internal server|csrf|blocked|suspended/.test(msgLower)) {
    return false;
  }
  if (isAwsWafChallengeResponse(result.status, result.rawText, result.headers)) {
    return false;
  }
  if (/not\s*registered|user\s*not\s*found|does\s*not\s*exist|no\s*account|new\s*user|sign\s*up|signup|register\s*first|unregistered/.test(msgLower)) {
    return true;
  }
  return result.data?.statusCode === 999;
}

// Pre-warm browser in background (safe no-op on cloud runtimes without local Chromium)
export async function prewarmBrowser() {
  if (!canUseStealthBrowser()) return;
  if (isPrewarming || (prewarmedPage && prewarmedBrowser?.connected && (Date.now() - prewarmedAt < 180000))) return;
  isPrewarming = true;

  try {
    if (prewarmedBrowser) {
      await prewarmedBrowser.close().catch(() => {});
      prewarmedBrowser = null;
      prewarmedPage = null;
    }

    const { browser, page } = await launchStealthSwiggyBrowser();
    await page.goto('https://www.swiggy.com/restaurants', { waitUntil: 'domcontentloaded', timeout: 15000 }).catch(() => {});

    const wafToken = await waitForSwiggyWafCookie(page, 4000);
    if (!wafToken) {
      await browser.close().catch(() => {});
      return;
    }

    latestSharedWafToken = wafToken;
    latestSharedWafAt = Date.now();
    try { wafPool.seedToken(wafToken, { source: 'chromium' }); } catch {}

    prewarmedBrowser = browser;
    prewarmedPage = page;
    prewarmedAt = Date.now();
  } catch (err) {
    if (prewarmedBrowser) {
      await prewarmedBrowser.close().catch(() => {});
      prewarmedBrowser = null;
      prewarmedPage = null;
    }
  } finally {
    isPrewarming = false;
  }
}

// Universal cached / live AWS WAF token provider for both swiggy-bridge and swiggy-cart
export async function getLiveSwiggyWafToken(forceRefresh = false) {
  const now = Date.now();
  // Check shared pool token first:
  const poolToken = wafPool.getTokenSync?.();
  if (!forceRefresh && poolToken) {
    latestSharedWafToken = poolToken;
    latestSharedWafAt = Date.now();
    return poolToken;
  }
  if (!forceRefresh && latestSharedWafToken && (now - latestSharedWafAt < WAF_CACHE_TTL_MS)) {
    return latestSharedWafToken;
  }

  // 1. Check if prewarmedPage is alive and has an active WAF cookie (<5ms check):
  if (!forceRefresh && prewarmedPage && prewarmedBrowser?.connected) {
    try {
      const cookies = await prewarmedPage.cookies('https://www.swiggy.com').catch(() => []);
      const waf = cookies.find(c => c.name === 'aws-waf-token' && String(c.value || '').length > 50);
      if (waf && waf.value) {
        latestSharedWafToken = waf.value;
        latestSharedWafAt = Date.now();
        try { wafPool.seedToken(waf.value, { source: 'chromium' }); } catch {}
        return latestSharedWafToken;
      }
    } catch {}
  }

  // 2. Coalesce concurrent requests so we only launch one solver:
  if (wafSolvePromise) return wafSolvePromise;

  wafSolvePromise = (async () => {
    let browser = null;
    try {
      const launched = await launchStealthSwiggyBrowser();
      browser = launched.browser;
      const page = launched.page;

      await page.goto('https://www.swiggy.com/', {
        waitUntil: 'domcontentloaded',
        timeout: 30000
      }).catch(() => {});

      const token = await waitForSwiggyWafCookie(page, SWIGGY_WAF_COOKIE_WAIT_MS);
      if (token) {
        latestSharedWafToken = token;
        latestSharedWafAt = Date.now();
        try { wafPool.seedToken(token, { source: 'chromium' }); } catch {}
        // Allow challenge reload/navigation to settle
        await new Promise(r => setTimeout(r, 1500));
      }
      await browser.close().catch(() => {});
      return latestSharedWafToken || '';
    } catch (err) {
      if (browser) await browser.close().catch(() => {});
      console.warn('[SwiggyBridge] WAF solver error:', err.message);
      return latestSharedWafToken || '';
    } finally {
      wafSolvePromise = null;
    }
  })();

  return wafSolvePromise;
}

export async function safeEvaluateAuthOnce(page, fn, ...args) {
  let timeoutId;
  try {
    // Auth POSTs must execute once only: retrying after a CDP timeout can send a duplicate OTP.
    return await Promise.race([
      page.evaluate(fn, ...args),
      new Promise((_, reject) => {
        timeoutId = setTimeout(
          () => reject(new Error(`Auth browser request timed out after ${AUTH_PAGE_EVALUATE_TIMEOUT_MS}ms; no automatic retry was attempted.`)),
          AUTH_PAGE_EVALUATE_TIMEOUT_MS
        );
      })
    ]);
  } finally {
    if (timeoutId) clearTimeout(timeoutId);
  }
}

export function parseSwiggyOtpError(otpResult) {
  if (!otpResult) {
    return {
      code: 'NO_RESPONSE',
      retryable: true,
      message: 'Swiggy ne OTP request ka response nahi diya. Network check karke baad mein ek baar retry karein.',
      swiggyStatus: 'No Response',
      details: 'Empty response from Swiggy'
    };
  }

  const swiggyMsg = (otpResult.data?.statusMessage || otpResult.data?.message || '').trim();
  const rawLower = ((otpResult.rawText || '') + ' ' + swiggyMsg).toLowerCase();
  const status = Number(otpResult.status || 0);
  const swiggyCode = Number(otpResult.data?.statusCode);

  if (status === 429 || swiggyCode === 429 || /rate limit|too many|limit reached|maximum attempts/.test(rawLower)) {
    return {
      code: 'SWIGGY_RATE_LIMIT',
      retryable: false,
      message: 'Swiggy ne OTP requests par temporary limit lagayi hai. Abhi dobara request na bhejein; 15–30 minute rukkar official Swiggy app/site se try karein. Repeated attempts limit ko badha sakte hain.',
      swiggyStatus: swiggyMsg || 'Swiggy Rate Limit (429 Too Many Requests)',
      details: `HTTP ${status || 429} | Swiggy rate limit`
    };
  }

  if (isCsrfMismatchResponse(status, otpResult.rawText || '', otpResult.data)) {
    return {
      code: 'SWIGGY_CSRF_EXPIRED',
      retryable: true,
      message: 'Swiggy session token refresh ho gaya hai. Ek baar Retry OTP dabayein.',
      swiggyStatus: swiggyMsg || 'Session CSRF Refresh Needed',
      details: `HTTP ${status || 403} | CSRF token refresh required`
    };
  }

  if (
    status === 202 ||
    isAwsWafChallengeResponse(status, otpResult.rawText || '', otpResult.headers) ||
    (status === 403 && !/csrf/.test(rawLower)) ||
    /waf|captcha|challenge|security check|access denied|verify you are human|bot verification|automated traffic/.test(rawLower)
  ) {
    return {
      code: 'SWIGGY_SECURITY_CHALLENGE',
      retryable: false,
      message: 'Swiggy security verification stopped this OTP request. This bot will not retry or bypass that check. Complete any verification in the official Swiggy app/site, or use an existing session export; try again later only if Swiggy allows it.',
      swiggyStatus: swiggyMsg || 'Security challenge (HTTP 403)',
      details: `HTTP ${status || 403} | Swiggy security challenge; no automated retry attempted`
    };
  }

  if (status === 400 || status === 422 || /invalid mobile|valid 10 digit/.test(rawLower)) {
    return {
      code: 'INVALID_MOBILE',
      retryable: false,
      message: `Swiggy rejected the number (${swiggyMsg || 'invalid format'}). Send a standalone valid Indian mobile number: 10 digits, or 12 digits beginning with 91.`,
      swiggyStatus: swiggyMsg || 'Invalid Mobile Number',
      details: `HTTP ${status || 400}`
    };
  }

  if ([500, 502, 503, 504].includes(status)) {
    return {
      code: 'SWIGGY_SERVER_ERROR',
      retryable: true,
      message: `Swiggy returned a temporary server error (HTTP ${status}). Wait a minute or two before retrying.`,
      swiggyStatus: swiggyMsg || `Swiggy Server Error (${status})`,
      details: `HTTP ${status}`
    };
  }

  if (otpResult.error) {
    return {
      code: 'SYSTEM_ERROR',
      retryable: true,
      message: `Could not complete the OTP request: ${otpResult.error}`,
      swiggyStatus: otpResult.error,
      details: 'Network or session context error'
    };
  }

  if (swiggyMsg) {
    return {
      code: 'SWIGGY_ERROR',
      retryable: true,
      message: `Swiggy rejected the OTP request: ${swiggyMsg} (HTTP ${status || 200}).`,
      swiggyStatus: swiggyMsg,
      details: `HTTP ${status || 200} | Swiggy Code: ${otpResult.data?.statusCode ?? 'none'}`
    };
  }

  return {
    code: 'SWIGGY_ERROR',
    retryable: true,
    message: `Swiggy did not confirm the OTP request (HTTP ${status || 'unknown'}). Check the official Swiggy app/site or try an existing session export.`,
    swiggyStatus: `HTTP ${status || 'unknown'} - OTP not confirmed`,
    details: `HTTP ${status || 'unknown'}`
  };
}

const otpInFlightByPhone = new Map();
const recentOtpDispatches = new Map();

function closeBridgeSessionCleanly(session) {
  if (!session) return;
  try {
    if (session.safetyTimer) clearTimeout(session.safetyTimer);
    if (session.browser) session.browser.close().catch(() => {});
  } catch {}
}

export async function requestSwiggyOtpViaBridge(userId, phone, targetAcc = '', targetAccName = null) {
  const cleanPhone = normalizeIndianMobileNumber(phone) || '';

  if (cleanPhone.length !== 10) {
    return { success: false, code: 'INVALID_MOBILE', message: 'Send a standalone 10-digit Indian mobile number or a 12-digit number beginning with 91.' };
  }

  const inflightKey = `${userId}:${cleanPhone}`;
  if (otpInFlightByPhone.has(inflightKey)) {
    return otpInFlightByPhone.get(inflightKey);
  }

  // Prevent accidental double-tap within 3.5s from firing 2 simultaneous SMS requests & burning Swiggy's rate limit!
  const recentHit = recentOtpDispatches.get(inflightKey);
  if (recentHit && (Date.now() - recentHit.ts < 3500) && activeSessions[userId]?.phone === cleanPhone) {
    if (targetAcc) activeSessions[userId].targetAcc = targetAcc;
    if (targetAccName) activeSessions[userId].targetAccName = targetAccName;
    return {
      success: true,
      phone: cleanPhone,
      isNewUser: Boolean(activeSessions[userId].isNewUser),
      deduplicated: true,
      message: 'OTP Sent',
      swiggyStatus: 'OTP Sent'
    };
  }

  const runPromise = (async () => {
    if (activeSessions[userId]) {
      closeBridgeSessionCleanly(activeSessions[userId]);
      delete activeSessions[userId];
    }

    const session = createSwiggyHttpAuthSession(cleanPhone, targetAcc || `acc_${cleanPhone}`, targetAccName || null);

    try {
      // Step 1: Dispatch primary SMS OTP with live `_csrf` + realistic mobile device cookies/headers (~350-600ms total!)
      let otpResult = await postSwiggyAuthJson(session, 'https://www.swiggy.com/dapi/auth/sms-otp', {
        mobile: cleanPhone
      });

      const msgLower = `${otpResult.data?.statusMessage || ''} ${otpResult.data?.message || ''} ${otpResult.rawText || ''}`.toLowerCase();
      const isRateOrInvalid =
        otpResult.status === 429 ||
        /rate limit|too many|limit reached|maximum|valid 10 digit|invalid mobile/.test(msgLower);
      const isSecurityBlocked = isAwsWafChallengeResponse(otpResult.status, otpResult.rawText, otpResult.headers) ||
        (otpResult.status === 403 && !isCsrfMismatchResponse(otpResult.status, otpResult.rawText, otpResult.data));

      // Fallback to `/dapi/auth/otp-generate` ONLY when `/dapi/auth/sms-otp` returned an unexpected non-200/non-unregistered status
      if (
        !isRateOrInvalid &&
        !isSecurityBlocked &&
        !isUnregisteredSwiggyAuthResponse(otpResult) &&
        (otpResult.status !== 200 || (otpResult.data?.statusCode && otpResult.data.statusCode !== 0 && otpResult.data.statusCode !== 1))
      ) {
        const altOut = await postSwiggyAuthJson(session, 'https://www.swiggy.com/dapi/auth/otp-generate', {
          mobile: cleanPhone
        }, { allowBrowserEscalation: false });
        if (altOut.status === 200 && (altOut.data?.statusCode === 0 || altOut.data?.statusCode === undefined)) {
          otpResult = altOut;
        }
      }

      // Check if number is unregistered / brand-new on Swiggy (including bare `statusCode: 1` verified via `signin-with-check` or explicit message)
      let isUnregistered = isUnregisteredSwiggyAuthResponse(otpResult);
      if (!isUnregistered && !isRateOrInvalid && !isSecurityBlocked && otpResult.status === 200 && otpResult.data?.statusCode === 1) {
        const bareMsg = String(otpResult.data?.statusMessage || otpResult.data?.message || '').trim().toLowerCase();
        if (!bareMsg) {
          const chkOut = await postSwiggyAuthJson(session, 'https://www.swiggy.com/dapi/auth/signin-with-check', {
            mobile: cleanPhone
          }, { allowBrowserEscalation: false }).catch(() => null);
          if (chkOut && (isUnregisteredSwiggyAuthResponse(chkOut) || chkOut.data?.data?.registered === false || chkOut.data?.type === 'register' || chkOut.data?.statusCode === 1)) {
            isUnregistered = true;
          }
        }
      }

      if (isUnregistered) {
        const signupName = sanitizeSwiggyName(targetAccName);
        let signupEmail = generateUniqueSwiggyEmail(cleanPhone, signupName);
        console.log(`[SwiggyBridge] Number ${cleanPhone} is new/unregistered on Swiggy. Dispatching signup flow as "${signupName}" (${signupEmail})...`);

        let signupInitResult = await postSwiggyAuthJson(session, 'https://www.swiggy.com/dapi/auth/signup', {
          mobile: cleanPhone,
          name: signupName,
          email: signupEmail,
          password: '',
          referral_code: ''
        });

        const initMsgLower = `${signupInitResult.data?.statusMessage || ''} ${signupInitResult.data?.message || ''} ${signupInitResult.rawText || ''}`.toLowerCase();
        // If generated email collided with an archived record, regenerate once and retry cleanly
        if (signupInitResult.status === 200 && signupInitResult.data?.statusCode !== 0 && /email.*exist|email.*already|duplicate.*email|invalid.*email/i.test(initMsgLower)) {
          signupEmail = generateUniqueSwiggyEmail(cleanPhone, `${signupName}x`);
          signupInitResult = await postSwiggyAuthJson(session, 'https://www.swiggy.com/dapi/auth/signup', {
            mobile: cleanPhone,
            name: signupName,
            email: signupEmail,
            password: '',
            referral_code: ''
          }, { allowBrowserEscalation: false });
        }

        const finalInitLower = `${signupInitResult.data?.statusMessage || ''} ${signupInitResult.data?.message || ''} ${signupInitResult.rawText || ''}`.toLowerCase();
        const signupSecurityBlocked = isAwsWafChallengeResponse(signupInitResult.status, signupInitResult.rawText, signupInitResult.headers) ||
          signupInitResult.status === 429 ||
          /rate limit|too many|limit reached/.test(finalInitLower);

        let signupPreRegistered = false;
        let signupOtpDispatched = false;

        if (!signupSecurityBlocked && signupInitResult.status === 200 && (signupInitResult.data?.statusCode === 0 || signupInitResult.data?.statusCode === undefined)) {
          signupPreRegistered = true;
          signupOtpDispatched = true;
        } else if (!signupSecurityBlocked && /otp.*required|enter.*otp|invalid.*otp/i.test(finalInitLower)) {
          // Cluster requires `sms-otp` (with `type: 'register'`) first and `signup` WITH `otp` on verification!
          const regSms = await postSwiggyAuthJson(session, 'https://www.swiggy.com/dapi/auth/sms-otp', {
            mobile: cleanPhone,
            type: 'register'
          }, { allowBrowserEscalation: false });
          if (regSms.status === 200 && (regSms.data?.statusCode === 0 || regSms.data?.statusCode === undefined)) {
            signupOtpDispatched = true;
          } else {
            signupInitResult = regSms;
          }
        }

        if (signupOtpDispatched) {
          session.isNewUser = true;
          session.signupPreRegistered = signupPreRegistered;
          session.signupName = signupName;
          session.signupEmail = signupEmail;
          session.targetAccName = String(targetAccName || signupName).trim() || signupName;
          session.safetyTimer = setTimeout(() => {
            if (activeSessions[userId] === session) {
              closeBridgeSessionCleanly(session);
              delete activeSessions[userId];
            }
          }, 600_000);

          activeSessions[userId] = session;
          recentOtpDispatches.set(inflightKey, { ts: Date.now() });

          return {
            success: true,
            phone: cleanPhone,
            isNewUser: true,
            message: 'OTP Sent',
            swiggyStatus: 'OTP Sent'
          };
        }

        closeBridgeSessionCleanly(session);
        const parsedErr = parseSwiggyOtpError(signupInitResult);
        return {
          success: false,
          code: parsedErr.code,
          retryable: parsedErr.retryable,
          message: parsedErr.message,
          swiggyStatus: parsedErr.swiggyStatus,
          details: parsedErr.details
        };
      }

      const isSent = !isRateOrInvalid && !isSecurityBlocked && otpResult.status === 200 && (
        otpResult.data?.statusCode === 0 || otpResult.data?.statusCode === undefined
      );

      if (isSent) {
        const defaultSignupName = sanitizeSwiggyName(targetAccName);
        session.isNewUser = false;
        session.signupName = defaultSignupName;
        session.signupEmail = generateUniqueSwiggyEmail(cleanPhone, defaultSignupName);
        session.safetyTimer = setTimeout(() => {
          if (activeSessions[userId] === session) {
            closeBridgeSessionCleanly(session);
            delete activeSessions[userId];
          }
        }, 600_000);

        activeSessions[userId] = session;
        recentOtpDispatches.set(inflightKey, { ts: Date.now() });

        return {
          success: true,
          phone: cleanPhone,
          message: 'OTP Sent',
          swiggyStatus: 'OTP Sent'
        };
      }

      closeBridgeSessionCleanly(session);
      const parsedErr = parseSwiggyOtpError(otpResult);
      return {
        success: false,
        code: parsedErr.code,
        retryable: parsedErr.retryable,
        message: parsedErr.message,
        swiggyStatus: parsedErr.swiggyStatus,
        details: parsedErr.details
      };
    } catch (err) {
      closeBridgeSessionCleanly(session);
      delete activeSessions[userId];
      const lower = String(err.message || '').toLowerCase();
      const inferredStatus = /429|rate limit|too many requests/.test(lower)
        ? 429
        : (/waf|captcha|challenge|verify you are human|bot verification|automated traffic/.test(lower) ? 403 : 500);
      const diagnostic = parseSwiggyOtpError({
        status: inferredStatus,
        error: err.message,
        data: { statusMessage: err.message }
      });
      return {
        success: false,
        code: diagnostic.code,
        retryable: diagnostic.retryable,
        message: diagnostic.message,
        swiggyStatus: diagnostic.swiggyStatus,
        details: err.stack ? err.stack.split('\n')[0] : diagnostic.details
      };
    }
  })();

  otpInFlightByPhone.set(inflightKey, runPromise);
  try {
    return await runPromise;
  } finally {
    otpInFlightByPhone.delete(inflightKey);
  }
}

async function resolveDeleteCookieJarAndCsrf(acc, cleanPhone = '', targetAcc = '', db = null) {
  let effectiveAcc = acc ? { ...acc } : null;
  if (!effectiveAcc && db) {
    const vaultEntry = (cleanPhone && db.sessionVault?.[cleanPhone]) || (targetAcc && db.sessionVault?.[targetAcc]) || null;
    if (vaultEntry) effectiveAcc = { ...vaultEntry };
  }
  if (effectiveAcc && db && !String(effectiveAcc.cookies || '').includes('_session_tid=')) {
    const vaultEntry = (cleanPhone && db.sessionVault?.[cleanPhone]) || (targetAcc && db.sessionVault?.[targetAcc]) || null;
    if (vaultEntry?.cookies?.includes('_session_tid=')) {
      effectiveAcc.cookies = `${vaultEntry.cookies}; ${effectiveAcc.cookies || ''}`;
    }
  }

  let cookieString = stripStaleWafCookie(cleanEssentialSwiggyCookies(effectiveAcc?.cookies || '', effectiveAcc || {}));

  // Auto-mint `_session_tid` if account was imported with Android tokens (`tid` + `token`) without web `_session_tid`!
  if (!cookieString.includes('_session_tid=') && effectiveAcc && (effectiveAcc.tid || effectiveAcc.token)) {
    try {
      const { bootstrapSwiggyWebSessionFromAndroidTokens } = await import('./swiggy-cart.js');
      const minted = await bootstrapSwiggyWebSessionFromAndroidTokens(effectiveAcc, 3500);
      if (minted) {
        cookieString = stripStaleWafCookie(minted);
      }
    } catch {}
  }

  const cookieMap = new Map();
  for (const part of cookieString.split(';')) {
    const trimmed = part.trim();
    if (!trimmed || !trimmed.includes('=')) continue;
    const eq = trimmed.indexOf('=');
    cookieMap.set(trimmed.slice(0, eq).trim(), trimmed.slice(eq + 1).trim());
  }
  return { effectiveAcc, cookieString, cookieMap };
}

async function ensureDeleteCsrfToken(cookieMap, currentCsrf = '', deviceProfile = null) {
  if (currentCsrf && cookieMap.has('_csrf')) return currentCsrf;
  const dev = deviceProfile || buildAntiBotDeviceProfile('');

  try {
    const res = await fetch('https://www.swiggy.com/web-cart-add-address', {
      method: 'GET',
      headers: {
        'Cookie': serializeCookieMap(cookieMap),
        'User-Agent': dev.ua,
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
        'X-Requested-With': 'in.swiggy.android'
      },
      redirect: 'manual',
      signal: AbortSignal.timeout(3000)
    });
    applySetCookiesToMap(cookieMap, getResponseSetCookies(res));
    const html = await res.text().catch(() => '');
    const m = html.match(/window\._csrf\s*=\s*["']([^"']+)["']/) || html.match(/csrfToken["']?\s*:\s*["']([^"']+)["']/);
    if (m && m[1]) return m[1];
  } catch {}

  try {
    const res = await fetch('https://www.swiggy.com/dapi/order/all', {
      method: 'GET',
      headers: {
        'Cookie': serializeCookieMap(cookieMap),
        'User-Agent': 'Swiggy-Android',
        'Accept': 'application/json',
        'Referer': 'https://www.swiggy.com/my-account'
      },
      signal: AbortSignal.timeout(3000)
    });
    applySetCookiesToMap(cookieMap, getResponseSetCookies(res));
    const j = await res.json().catch(() => null);
    if (j?.csrfToken) return String(j.csrfToken);
  } catch {}

  return currentCsrf || cookieMap.get('_csrf') || '';
}

export async function requestSwiggyDeleteOtpViaBridge(userId, phone, targetAcc = '', targetAccName = null) {
  const cleanPhone = normalizeIndianMobileNumber(phone) || '';
  if (!cleanPhone) {
    return { success: false, code: 'INVALID_MOBILE', message: 'Send a standalone 10-digit Indian mobile number or a 12-digit number beginning with 91.' };
  }

  delete activeDeleteSessions[userId];

  const { getDb } = await import('./store.js');
  const db = getDb();
  let acc = db.config?.accounts?.[targetAcc];

  if (!acc && cleanPhone) {
    for (const [k, a] of Object.entries(db.config?.accounts || {})) {
      const aPhone = normalizeIndianMobileNumber(a?.phone || a?.mobile || String(k).replace(/^acc_/, '')) || '';
      if (aPhone === cleanPhone && (a?.cookies || a?.tid || a?.token)) {
        acc = a;
        targetAcc = k;
        break;
      }
    }
  }

  const { effectiveAcc, cookieString, cookieMap } = await resolveDeleteCookieJarAndCsrf(acc, cleanPhone, targetAcc, db);

  if (!cookieString && !effectiveAcc?.tid && !effectiveAcc?.token) {
    return {
      success: false,
      isAuthError: true,
      message: 'Account session cookies not found. Please log in first or remove account from Bot DB.'
    };
  }

  const isAuth = checkLoggedInFromCookies(cookieString) || checkLoggedInFromCookies(effectiveAcc);
  if (!isAuth) {
    return {
      success: false,
      isAuthError: true,
      message: 'Selected account session is logged out or expired. Re-login or remove from Bot DB.'
    };
  }

  deleteOtpRequestCount++;
  const reqNum = deleteOtpRequestCount;
  const maskedPhone = cleanPhone.length >= 4 ? '******' + cleanPhone.slice(-4) : '***';
  const dev = buildAntiBotDeviceProfile(cleanPhone);
  console.log(`[SwiggyDelete] [Request #${reqNum}] Triggering Delete OTP: GET /mapi/auth/delete/userCheck | Target: ${targetAcc} | Phone: ${maskedPhone}`);

  try {
    const tidVal = effectiveAcc?.tid || cookieMap.get('tid') || '';
    const sidVal = effectiveAcc?.sid || cookieMap.get('_sid') || '';
    const tokVal = effectiveAcc?.token || cookieMap.get('token') || '';
    const devVal = effectiveAcc?.deviceId || cookieMap.get('_device_id') || dev.deviceId;

    const callUserCheck = async (useAndroidUa = false) => {
      const r = await fetch('https://www.swiggy.com/mapi/auth/delete/userCheck', {
        method: 'GET',
        headers: {
          'Cookie': serializeCookieMap(cookieMap),
          'User-Agent': useAndroidUa ? 'Swiggy-Android' : dev.ua,
          'Accept': 'application/json',
          'Referer': 'https://www.swiggy.com/my-account/settings',
          'Origin': 'https://www.swiggy.com',
          ...(tidVal ? { 'tid': tidVal } : {}),
          ...(sidVal ? { 'sid': sidVal } : {}),
          ...(tokVal ? { 'token': tokVal } : {}),
          ...(devVal ? { 'deviceId': devVal, 'swuid': devVal } : {})
        },
        signal: AbortSignal.timeout(8000)
      });
      applySetCookiesToMap(cookieMap, getResponseSetCookies(r));
      const txt = await r.text().catch(() => '');
      let parsed = {};
      try { parsed = JSON.parse(txt); } catch {}
      return { status: r.status, rawText: txt, data: parsed, headers: r.headers };
    };

    let checkOut = await callUserCheck(false);
    if (isAwsWafChallengeResponse(checkOut.status, checkOut.rawText, checkOut.headers)) {
      checkOut = await callUserCheck(true);
    }

    const { status, rawText, data, headers } = checkOut;
    const responseLower = `${rawText} ${data.statusMessage || data.message || data.error || ''}`.toLowerCase();

    if (isAwsWafChallengeResponse(status, rawText, headers)) {
      delete activeDeleteSessions[userId];
      return {
        success: false,
        code: 'SWIGGY_SECURITY_CHALLENGE',
        retryable: false,
        message: 'Swiggy security verification stopped the deletion OTP request. Complete any check in the official Swiggy app/site, or remove the account from this bot only.',
        swiggyStatus: `HTTP ${status} security challenge`,
        details: `HTTP ${status} | Swiggy security challenge`
      };
    }

    console.log(`[SwiggyDelete] [Request #${reqNum}] Response: HTTP ${status} | SwiggyCode: ${data.statusCode ?? 'none'} | Message: ${data.statusMessage || data.error || 'ok'}`);

    const isSent = status === 200 && (data.statusCode === 28 || data.statusCode === 0);

    if (!isSent) {
      if (status === 429 || /rate limit|too many|limit reached|maximum attempts/.test(responseLower)) {
        return {
          success: false,
          code: 'SWIGGY_RATE_LIMIT',
          retryable: false,
          message: 'Swiggy rate-limited the deletion OTP request. Wait 15–30 minutes and finish deletion through the official Swiggy app/site; do not retry repeatedly.',
          details: 'HTTP 429 | Swiggy rate limit'
        };
      }
      if (data.statusCode === 25) {
        return { success: false, message: 'You have pending cancellation charges on Swiggy. Please clear them first or remove from Bot DB only.' };
      }
      if (data.statusCode === 26) {
        return { success: false, message: 'An active order is in progress on this Swiggy account. Try again after delivery or remove from Bot DB only.' };
      }
      if (data.statusCode === 34) {
        return { success: false, message: 'Cannot delete on Swiggy while active Swiggy Money balance exists. Remove from Bot DB only if needed.' };
      }
      const isAuthError = status === 401 || data.statusCode === 1 || data.statusCode === 999 || /login|session expired|unauthorized/i.test(data.statusMessage || '');
      const errMsg = isAuthError
        ? 'Swiggy session has expired on Swiggy servers. Re-login or remove this account from Bot DB.'
        : (data.statusMessage || data.error || `Swiggy returned status ${status} (code ${data.statusCode ?? 'unknown'})`);
      return {
        success: false,
        isAuthError,
        message: errMsg,
        swiggyStatus: errMsg
      };
    }

    if (data.tid) cookieMap.set('tid', String(data.tid));
    if (data.sid) cookieMap.set('_sid', String(data.sid));
    let resolvedCsrf = data.csrfToken || data?.data?.csrfToken || '';
    if (!resolvedCsrf) {
      resolvedCsrf = await ensureDeleteCsrfToken(cookieMap, '', dev);
    }

    activeDeleteSessions[userId] = {
      accountKey: targetAcc,
      phone: cleanPhone,
      tid: data.tid || tidVal || '',
      token: tokVal || '',
      csrfToken: resolvedCsrf || '',
      sid: data.sid || sidVal || '',
      deviceId: data.deviceId || devVal || '',
      cookieMap,
      cookies: serializeCookieMap(cookieMap),
      deviceProfile: dev,
      createdAt: Date.now()
    };

    return {
      success: true,
      phone: cleanPhone,
      message: data.statusMessage || 'Archive OTP Sent',
      swiggyStatus: 'Swiggy Account Deletion OTP sent to ' + cleanPhone
    };
  } catch (err) {
    console.error(`[SwiggyDelete] [Request #${reqNum}] Exception calling /mapi/auth/delete/userCheck:`, err.message);
    return {
      success: false,
      message: 'Failed to contact Swiggy deletion endpoint: ' + err.message
    };
  }
}

export async function verifyAndDeleteSwiggyAccountViaBridge(userId, otp, accountKey) {
  const session = activeDeleteSessions[userId];
  const cleanOtp = String(otp).replace(/[^0-9]/g, '').trim();

  if (cleanOtp.length !== 6) {
    return { success: false, message: 'Please enter the exact 6-digit OTP.' };
  }

  const { getDb } = await import('./store.js');
  const db = getDb();
  const acc = db.config?.accounts?.[accountKey];
  const phone = normalizeIndianMobileNumber(session?.phone || acc?.phone || String(accountKey || '').replace(/^acc_/, '')) || (session?.phone || acc?.phone || '');
  const dev = session?.deviceProfile || buildAntiBotDeviceProfile(phone);

  let cookieMap = session?.cookieMap instanceof Map ? session.cookieMap : null;
  if (!cookieMap) {
    const resolved = await resolveDeleteCookieJarAndCsrf(acc, phone, accountKey, db);
    cookieMap = resolved.cookieMap;
  }

  if (cookieMap.size === 0) {
    return {
      success: false,
      message: 'Deletion session or cookies expired. Please tap Delete Account again to get a fresh OTP.'
    };
  }

  const tid = session?.tid || acc?.tid || cookieMap.get('tid') || '';
  const sid = session?.sid || acc?.sid || cookieMap.get('_sid') || '';
  const token = session?.token || acc?.token || cookieMap.get('token') || '';
  const deviceId = session?.deviceId || acc?.deviceId || cookieMap.get('_device_id') || dev.deviceId;
  if (tid && !cookieMap.has('tid')) cookieMap.set('tid', tid);
  if (sid && !cookieMap.has('_sid')) cookieMap.set('_sid', sid);

  let csrfToken = await ensureDeleteCsrfToken(cookieMap, session?.csrfToken || '', dev);

  deleteVerifyRequestCount++;
  const reqNum = deleteVerifyRequestCount;
  const maskedPhone = phone.length >= 4 ? '******' + phone.slice(-4) : '***';
  console.log(`[SwiggyDelete] [Verify #${reqNum}] Verifying Delete OTP: POST /mapi/auth/delete/user | Target: ${accountKey} | Phone: ${maskedPhone}`);

  try {
    const sendDeletePost = async (useAndroidUa = false) => {
      const r = await fetch('https://www.swiggy.com/mapi/auth/delete/user', {
        method: 'POST',
        headers: {
          'Cookie': serializeCookieMap(cookieMap),
          'User-Agent': useAndroidUa ? 'Swiggy-Android' : dev.ua,
          'Content-Type': 'application/json',
          'Accept': 'application/json',
          'Origin': 'https://www.swiggy.com',
          'Referer': 'https://www.swiggy.com/my-account/settings',
          ...(tid ? { 'tid': tid } : {}),
          ...(sid ? { 'sid': sid } : {}),
          ...(token ? { 'token': token } : {}),
          ...(deviceId ? { 'deviceId': deviceId, 'swuid': deviceId } : {})
        },
        body: JSON.stringify({ otp: cleanOtp, ...(csrfToken ? { _csrf: csrfToken } : {}) }),
        signal: AbortSignal.timeout(8500)
      });
      applySetCookiesToMap(cookieMap, getResponseSetCookies(r));
      const txt = await r.text().catch(() => '');
      let j = {};
      try { j = JSON.parse(txt); } catch {}
      return { status: r.status, rawText: txt, data: j, headers: r.headers };
    };

    let delOut = await sendDeletePost(false);

    // Auto-refresh CSRF once if HTTP 403/400 was due to stale CSRF secret (NOT AWS WAF!)
    if (isCsrfMismatchResponse(delOut.status, delOut.rawText, delOut.data)) {
      cookieMap.delete('_csrf');
      csrfToken = await ensureDeleteCsrfToken(cookieMap, '', dev);
      if (session) session.csrfToken = csrfToken;
      delOut = await sendDeletePost(false);
    }

    if (isAwsWafChallengeResponse(delOut.status, delOut.rawText, delOut.headers)) {
      delOut = await sendDeletePost(true);
    }

    const { status, rawText, data: verifyResult, headers } = delOut;
    const responseLower = `${rawText} ${verifyResult?.statusMessage || verifyResult?.message || verifyResult?.error || ''}`.toLowerCase();

    if (isAwsWafChallengeResponse(status, rawText, headers)) {
      delete activeDeleteSessions[userId];
      return {
        success: false,
        code: 'SWIGGY_SECURITY_CHALLENGE',
        retryable: false,
        message: 'Swiggy security verification stopped the deletion request. Finish account deletion in the official Swiggy app/site.',
        details: `HTTP ${status} | Swiggy security challenge`
      };
    }

    console.log(`[SwiggyDelete] [Verify #${reqNum}] Response: HTTP ${status} | SwiggyCode: ${verifyResult?.statusCode ?? 'none'} | Message: ${verifyResult?.statusMessage || verifyResult?.error || 'ok'}`);

    if (status === 429 || /rate limit|too many|limit reached|maximum attempts/.test(responseLower)) {
      delete activeDeleteSessions[userId];
      return {
        success: false,
        code: 'SWIGGY_RATE_LIMIT',
        retryable: false,
        message: 'Swiggy rate-limited deletion verification. Wait 15–30 minutes and use the official Swiggy app/site; do not repeatedly resend the OTP.',
        details: 'HTTP 429 | Swiggy rate limit'
      };
    }

    if (!verifyResult || verifyResult.error) {
      return {
        success: false,
        message: verifyResult?.error || 'Failed to communicate with Swiggy servers. Please try again.'
      };
    }

    if (verifyResult.statusCode === 29 || /invalid otp|incorrect otp|wrong otp/i.test(verifyResult.statusMessage || '')) {
      return {
        success: false,
        message: verifyResult.statusMessage || 'Invalid OTP. Please check and re-enter.'
      };
    }

    if (verifyResult.statusCode === 25) {
      delete activeDeleteSessions[userId];
      return { success: false, message: 'You have pending cancellation charges. Please clear them first on Swiggy.' };
    }
    if (verifyResult.statusCode === 26) {
      delete activeDeleteSessions[userId];
      return { success: false, message: 'You have an ongoing order. Please try after delivery.' };
    }
    if (verifyResult.statusCode === 34) {
      delete activeDeleteSessions[userId];
      return { success: false, message: 'Cannot delete: active Swiggy Money wallet exists.' };
    }

    const isSuccess = status === 200 && (
      verifyResult.statusCode === 33 ||
      verifyResult.statusCode === 0 ||
      (verifyResult.statusCode === undefined && !isCsrfMismatchResponse(status, rawText, verifyResult))
    );

    if (isSuccess) {
      delete activeDeleteSessions[userId];
      return {
        success: true,
        phone,
        message: verifyResult.statusMessage || 'Account permanently deleted from Swiggy servers!'
      };
    }

    return {
      success: false,
      message: verifyResult.statusMessage || `Deletion blocked by Swiggy (Code ${verifyResult.statusCode ?? status})`
    };
  } catch (err) {
    console.error(`[SwiggyDelete] [Verify #${reqNum}] Error in delete OTP verification:`, err.message);
    return { success: false, message: err.message };
  }
}

// Hydrate verified session profile (`customerId`, JWT `tid`, `token`, `swiggyName`, `0-Order` badge) + fast offer pre-lock
async function finalizeAuthenticatedSwiggyAccount(userId, session, authResult, { wasNewSignup = false, explicitName = '' } = {}) {
  const { phone, targetAcc } = session;

  if (session.page && session.browser?.connected) {
    const pageCookies = await waitForSwiggyLoginCookies(session.page, 500);
    for (const c of pageCookies) {
      if (c?.name && c?.value && c.name !== 'aws-waf-token') {
        session.cookieMap.set(c.name, c.value);
      }
    }
  }

  const resUserData = authResult?.data?.data || {};
  let tidVal = authResult?.data?.tid || session.cookieMap.get('tid') || '';
  let sidVal = authResult?.data?.sid || session.cookieMap.get('_sid') || '';
  let deviceIdVal = authResult?.data?.deviceId || session.cookieMap.get('_device_id') || session.deviceProfile?.deviceId || '';
  let tokenVal = resUserData.token || session.cookieMap.get('token') || '';
  let resolvedName = resUserData.name || '';
  let resolvedEmail = resUserData.email || session.signupEmail || '';
  let resolvedCustomerId = resUserData.customer_id || resUserData.user_id || resUserData.id || '';
  let totalOrdersCount = wasNewSignup ? 0 : undefined;

  if (tidVal) session.cookieMap.set('tid', String(tidVal));
  if (sidVal) session.cookieMap.set('_sid', String(sidVal));
  if (deviceIdVal) session.cookieMap.set('_device_id', String(deviceIdVal));
  if (tokenVal) session.cookieMap.set('token', String(tokenVal));
  session.cookieMap.set('_is_logged_in', '1');

  // Enrich real `customerId`, JWT `tid`, `token`, and `_session_tid` via fast ~160ms `/dapi/profile/info`
  try {
    const profRes = await fetch('https://www.swiggy.com/dapi/profile/info', {
      method: 'GET',
      headers: buildAuthRequestHeaders(session, { referer: 'https://www.swiggy.com/my-account', useAndroidUa: true }),
      signal: AbortSignal.timeout(2500)
    });
    applySetCookiesToMap(session.cookieMap, getResponseSetCookies(profRes));
    const profJson = await profRes.json().catch(() => null);
    if (profJson && profJson.statusCode === 0) {
      if (profJson.tid && String(profJson.tid).includes('.')) {
        tidVal = String(profJson.tid);
        session.cookieMap.set('tid', tidVal);
      }
      if (profJson.sid) {
        sidVal = String(profJson.sid);
        session.cookieMap.set('_sid', sidVal);
      }
      if (profJson.deviceId) {
        deviceIdVal = String(profJson.deviceId);
        session.cookieMap.set('_device_id', deviceIdVal);
      }
      const d = profJson.data || {};
      if (d.customer_id) resolvedCustomerId = String(d.customer_id);
      if (d.token) {
        tokenVal = String(d.token);
        session.cookieMap.set('token', tokenVal);
      }
      if (d.name && !resolvedName) resolvedName = String(d.name);
      if (d.email && !resolvedEmail) resolvedEmail = String(d.email);
    }
  } catch {}

  const jwtClaims = tidVal ? decodeJwtPayload(tidVal) : null;
  if (!resolvedCustomerId && jwtClaims?.user_id && String(jwtClaims.user_id) !== '0' && String(jwtClaims.user_id) !== '-1') {
    resolvedCustomerId = String(jwtClaims.user_id);
  }
  const customerId = resolvedCustomerId ? String(resolvedCustomerId) : '';

  // For existing accounts, do a quick ~250ms order-history peek so Vault immediately tags `0-Order` vs `Used`
  if (totalOrdersCount === undefined && session.cookieMap.has('_session_tid')) {
    try {
      const ordRes = await fetch('https://www.swiggy.com/dapi/order/all', {
        method: 'GET',
        headers: buildAuthRequestHeaders(session, { referer: 'https://www.swiggy.com/my-account', useAndroidUa: true }),
        signal: AbortSignal.timeout(2200)
      });
      applySetCookiesToMap(session.cookieMap, getResponseSetCookies(ordRes));
      const ordJson = await ordRes.json().catch(() => null);
      if (ordJson && ordJson.statusCode === 0) {
        if (!tidVal && ordJson.tid && String(ordJson.tid).includes('.')) {
          tidVal = String(ordJson.tid);
          session.cookieMap.set('tid', tidVal);
        }
        const ordersArr = Array.isArray(ordJson?.data?.orders) ? ordJson.data.orders : null;
        if (ordersArr) {
          totalOrdersCount = ordersArr.length;
        }
      }
    } catch {}
  }

  const rawCookieJoined = serializeCookieMap(session.cookieMap);
  const fullCookieStr = cleanEssentialSwiggyCookies(rawCookieJoined, {
    tid: tidVal,
    sid: sidVal,
    deviceId: deviceIdVal,
    token: tokenVal
  });

  const requestedAccountLabel = String(explicitName || session.targetAccName || '').trim();
  const rawSlot = requestedAccountLabel && !/^user\s*\d+$/i.test(requestedAccountLabel)
    ? requestedAccountLabel
    : getNextAutoUserName();
  const cleanActual = String(resolvedName || session.signupName || '').replace(/\([^)]*\)/g, '').trim();
  const finalName = rawSlot || cleanActual || getNextAutoUserName();
  const accKey = targetAcc || `acc_${phone}`;

  // Fast sub-second Today+Tomorrow offer pre-lock (bounded at 2.4s max so OTP verification NEVER stalls!)
  let offersResult = { success: false, pendingBackgroundLock: true };
  try {
    offersResult = await Promise.race([
      claimSwiggyBreakfastAndLateNightOffers({
        id: accKey,
        phone,
        token: tokenVal || tidVal,
        tid: tidVal,
        sid: sidVal,
        deviceId: deviceIdVal,
        cookies: fullCookieStr
      }, { quickLockOnly: true }),
      new Promise(resolve => setTimeout(() => resolve({ success: false, pendingBackgroundLock: true }), 2400))
    ]);
  } catch {}

  const savedData = {
    name: finalName,
    swiggyName: cleanActual || '',
    botTag: rawSlot,
    email: resolvedEmail,
    phone,
    mobile: phone,
    customerId,
    tid: tidVal || '',
    sid: sidVal || '',
    deviceId: deviceIdVal || '',
    token: tokenVal || tidVal || '',
    ...(typeof totalOrdersCount === 'number' ? {
      totalOrdersCount,
      isZeroOrderAccount: totalOrdersCount === 0
    } : {}),
    isLoggedIn: true,
    cookies: fullCookieStr,
    offers: offersResult,
    savedAt: new Date().toISOString()
  };

  const persisted = updateAccount(accKey, savedData);
  const finalSavedKey = persisted?.id || accKey;

  closeBridgeSessionCleanly(session);
  delete activeSessions[userId];

  const exportJson = {
    account: finalSavedKey,
    name: finalName,
    swiggyName: cleanActual || '',
    botTag: rawSlot,
    mobile: phone,
    phone,
    customerId,
    token: savedData.token,
    tid: savedData.tid,
    sid: savedData.sid,
    deviceId: savedData.deviceId,
    cookies: fullCookieStr,
    savedAt: savedData.savedAt
  };

  return {
    success: true,
    isNewUser: false,
    wasNewSignup,
    name: finalName,
    swiggyName: cleanActual || '',
    botTag: rawSlot,
    accountKey: finalSavedKey,
    phone,
    customerId: customerId || 'Verified',
    totalOrdersCount,
    isZeroOrderAccount: totalOrdersCount === 0,
    offers: offersResult,
    exportJson,
    message: authResult?.data?.statusMessage || (wasNewSignup ? 'Swiggy account created and logged in successfully!' : 'done successfully'),
    swiggyStatus: authResult?.data?.statusMessage || 'done successfully'
  };
}

export async function verifySwiggyOtpViaBridge(userId, otp) {
  const session = activeSessions[userId];
  if (!session) {
    return { success: false, message: 'Session expired. Please enter phone number again.' };
  }

  const cleanOtp = String(otp).replace(/[^0-9]/g, '').trim();
  if (cleanOtp.length !== 6) {
    return { success: false, message: 'Please enter the exact 6-digit OTP.' };
  }

  // Always persist `session.otp` immediately so follow-up `signupSwiggyViaBridge` NEVER fails with missing OTP!
  session.otp = cleanOtp;
  const { phone } = session;

  try {
    let verifyResult = null;
    let statusCode = null;
    let statusMsg = '';
    let isSuccess = false;
    let usedSignupCompletion = false;

    // Try standard `otp-verify` whenever existing user OR when `signup` pre-registered the mobile in Step 1!
    if (!session.isNewUser || session.signupPreRegistered) {
      verifyResult = await postSwiggyAuthJson(session, 'https://www.swiggy.com/dapi/auth/otp-verify', {
        mobile: phone,
        otp: cleanOtp
      });

      statusCode = verifyResult?.data?.statusCode;
      statusMsg = String(verifyResult?.data?.statusMessage || verifyResult?.data?.message || '').trim();
      isSuccess = (verifyResult?.status === 200 || verifyResult?.status === 202) && statusCode === 0;

      const verifyLower = `${verifyResult?.rawText || ''} ${statusMsg}`.toLowerCase();
      const verificationBlocked = isAwsWafChallengeResponse(verifyResult?.status, verifyResult?.rawText, verifyResult?.headers);
      const verificationRateLimited = verifyResult?.status === 429 || /rate limit|too many|limit reached|maximum attempts/.test(verifyLower);

      if (verificationBlocked || verificationRateLimited) {
        closeBridgeSessionCleanly(session);
        delete activeSessions[userId];
        const diagnostic = parseSwiggyOtpError(verifyResult);
        return {
          success: false,
          code: diagnostic.code,
          retryable: false,
          swiggyStatus: diagnostic.swiggyStatus,
          message: diagnostic.message
        };
      }
    }

    const msgLower = statusMsg.toLowerCase();
    const isExplicitWrongOtp = /invalid otp|incorrect otp|wrong otp|otp expired|expired otp|enter valid otp/.test(msgLower);
    const needsNewSignupCompletion = !isSuccess && !isExplicitWrongOtp && (
      session.isNewUser ||
      isUnregisteredSwiggyAuthResponse(verifyResult) ||
      msgLower.includes('invalid mobile number')
    );

    if (!isSuccess && statusCode === 1 && !needsNewSignupCompletion) {
      if (session.safetyTimer) clearTimeout(session.safetyTimer);
      session.safetyTimer = setTimeout(() => {
        if (activeSessions[userId] === session) {
          closeBridgeSessionCleanly(session);
          delete activeSessions[userId];
        }
      }, 300_000);

      return {
        success: false,
        swiggyStatus: statusMsg || 'Galat OTP (Invalid OTP)',
        message: statusMsg || 'Galat OTP enter kiya hai. Kripya check karke dubara daalein.'
      };
    }

    if (needsNewSignupCompletion) {
      const signupName = session.signupName || sanitizeSwiggyName(session.targetAccName);
      let signupEmail = session.signupEmail || generateUniqueSwiggyEmail(phone, signupName);
      session.signupName = signupName;
      session.signupEmail = signupEmail;
      console.log(`[SwiggyBridge] Completing fresh Swiggy signup for ${phone} as "${signupName}" (${signupEmail})...`);

      let signupResult = await postSwiggyAuthJson(session, 'https://www.swiggy.com/dapi/auth/signup', {
        mobile: phone,
        otp: cleanOtp,
        name: signupName,
        email: signupEmail,
        password: '',
        referral_code: ''
      });

      const sLower = `${signupResult?.data?.statusMessage || ''} ${signupResult?.data?.message || ''} ${signupResult?.rawText || ''}`.toLowerCase();
      if (signupResult?.status === 200 && signupResult?.data?.statusCode !== 0 && /email.*exist|email.*already|duplicate.*email/i.test(sLower)) {
        signupEmail = generateUniqueSwiggyEmail(phone, `${signupName}z`);
        session.signupEmail = signupEmail;
        signupResult = await postSwiggyAuthJson(session, 'https://www.swiggy.com/dapi/auth/signup', {
          mobile: phone,
          otp: cleanOtp,
          name: signupName,
          email: signupEmail,
          password: '',
          referral_code: ''
        }, { allowBrowserEscalation: false });
      }

      if (signupResult?.status === 200 && (signupResult?.data?.statusCode === 0 || signupResult?.data?.statusCode === undefined)) {
        verifyResult = signupResult;
        statusCode = 0;
        statusMsg = signupResult?.data?.statusMessage || 'done successfully';
        isSuccess = true;
        usedSignupCompletion = true;
      } else {
        const errMessage = signupResult?.data?.statusMessage || signupResult?.error || 'Invalid or expired Signup OTP';
        const diagnostic = signupResult ? parseSwiggyOtpError(signupResult) : null;
        if (diagnostic && ['SWIGGY_SECURITY_CHALLENGE', 'SWIGGY_RATE_LIMIT'].includes(diagnostic.code)) {
          closeBridgeSessionCleanly(session);
          delete activeSessions[userId];
          return {
            success: false,
            code: diagnostic.code,
            retryable: false,
            swiggyStatus: diagnostic.swiggyStatus,
            message: diagnostic.message
          };
        }
        return {
          success: false,
          swiggyStatus: errMessage,
          message: errMessage
        };
      }
    }

    const cookieCheckStr = serializeCookieMap(session.cookieMap);
    const isReallyLoggedIn = checkLoggedInFromCookies(cookieCheckStr);

    if (!isSuccess && !isReallyLoggedIn) {
      if (session.safetyTimer) clearTimeout(session.safetyTimer);
      session.safetyTimer = setTimeout(() => {
        if (activeSessions[userId] === session) {
          closeBridgeSessionCleanly(session);
          delete activeSessions[userId];
        }
      }, 300_000);

      const errReason = statusMsg || verifyResult?.error || (verifyResult?.status === 429 ? 'Maximum OTP verification attempts exceeded' : 'Invalid or expired OTP');
      return {
        success: false,
        swiggyStatus: errReason,
        message: errReason
      };
    }

    return await finalizeAuthenticatedSwiggyAccount(userId, session, verifyResult, {
      wasNewSignup: Boolean(session.isNewUser || usedSignupCompletion)
    });
  } catch (err) {
    return {
      success: false,
      isNewUser: false,
      swiggyStatus: err.message,
      message: `System Error: ${err.message}`
    };
  }
}

export async function signupSwiggyViaBridge(userId, enteredName, enteredEmail = null) {
  const session = activeSessions[userId];
  if (!session || !session.otp) {
    return { success: false, message: 'Session expired. Please enter phone number again.' };
  }

  const { phone, otp } = session;
  const cleanName = sanitizeSwiggyName(enteredName || session.targetAccName);
  const accountLabel = String(session.targetAccName || enteredName || cleanName).trim() || cleanName;
  let signupEmail = (enteredEmail && String(enteredEmail).includes('@'))
    ? String(enteredEmail).trim()
    : (session.signupEmail || generateUniqueSwiggyEmail(phone, cleanName));

  try {
    let signupResult = await postSwiggyAuthJson(session, 'https://www.swiggy.com/dapi/auth/signup', {
      mobile: phone,
      otp,
      name: cleanName,
      email: signupEmail,
      password: '',
      referral_code: ''
    });

    const sLower = `${signupResult?.data?.statusMessage || ''} ${signupResult?.data?.message || ''} ${signupResult?.rawText || ''}`.toLowerCase();
    if (!enteredEmail && signupResult?.status === 200 && signupResult?.data?.statusCode !== 0 && /email.*exist|email.*already|duplicate.*email/i.test(sLower)) {
      signupEmail = generateUniqueSwiggyEmail(phone, `${cleanName}r`);
      session.signupEmail = signupEmail;
      signupResult = await postSwiggyAuthJson(session, 'https://www.swiggy.com/dapi/auth/signup', {
        mobile: phone,
        otp,
        name: cleanName,
        email: signupEmail,
        password: '',
        referral_code: ''
      }, { allowBrowserEscalation: false });
    }

    const isReallyLoggedIn = checkLoggedInFromCookies(serializeCookieMap(session.cookieMap));

    if (
      isReallyLoggedIn ||
      (signupResult?.status === 200 && (signupResult?.data?.statusCode === 0 || signupResult?.data?.statusCode === undefined))
    ) {
      session.signupEmail = signupEmail;
      session.signupName = cleanName;
      return await finalizeAuthenticatedSwiggyAccount(userId, session, signupResult, {
        wasNewSignup: true,
        explicitName: accountLabel
      });
    }

    const errorMsg =
      signupResult?.data?.statusMessage ||
      signupResult?.error ||
      'Failed to signup on Swiggy';
    const diagnostic = parseSwiggyOtpError(signupResult || {});
    if (['SWIGGY_SECURITY_CHALLENGE', 'SWIGGY_RATE_LIMIT'].includes(diagnostic.code)) {
      closeBridgeSessionCleanly(session);
      delete activeSessions[userId];
      return {
        success: false,
        code: diagnostic.code,
        retryable: false,
        message: diagnostic.message,
        swiggyStatus: diagnostic.swiggyStatus
      };
    }
    return { success: false, message: errorMsg };
  } catch (err) {
    const diagnostic = parseSwiggyOtpError({
      status: /429|rate limit|too many/i.test(err.message || '') ? 429 : (/waf|captcha|challenge/i.test(err.message || '') ? 403 : 500),
      error: err.message,
      data: { statusMessage: err.message }
    });
    if (['SWIGGY_SECURITY_CHALLENGE', 'SWIGGY_RATE_LIMIT'].includes(diagnostic.code)) {
      closeBridgeSessionCleanly(session);
      delete activeSessions[userId];
      return { success: false, code: diagnostic.code, retryable: false, message: diagnostic.message };
    }
    return { success: false, code: diagnostic.code, retryable: diagnostic.retryable, message: err.message };
  }
}

// Closes any open session for `targetAcc` cleanly without clobbering an unrelated in-flight login session!
export async function deactivateSwiggyAccountViaBridge(userId, targetAcc, revokeRemote = false) {
  const session = activeSessions[userId];
  if (session && (!targetAcc || session.targetAcc === targetAcc || `acc_${session.phone}` === targetAcc)) {
    closeBridgeSessionCleanly(session);
    delete activeSessions[userId];
  }
  const delSession = activeDeleteSessions[userId];
  if (delSession && (!targetAcc || delSession.accountKey === targetAcc || `acc_${delSession.phone}` === targetAcc)) {
    delete activeDeleteSessions[userId];
  }

  if (revokeRemote) {
    try {
      const { getDb } = await import('./store.js');
      const db = getDb();
      const acc = db.config?.accounts?.[targetAcc];
      const cleanCk = stripStaleWafCookie(acc?.cookies || '');
      if (cleanCk) {
        const cookieMap = new Map();
        for (const p of cleanCk.split(';')) {
          const t = p.trim();
          const eq = t.indexOf('=');
          if (eq > 0) cookieMap.set(t.slice(0, eq).trim(), t.slice(eq + 1).trim());
        }
        const csrf = await ensureDeleteCsrfToken(cookieMap, '', buildAntiBotDeviceProfile(acc?.phone || ''));
        await fetch('https://www.swiggy.com/dapi/auth/logout', {
          method: 'POST',
          headers: {
            'Content-Type': 'application/json',
            'Accept': 'application/json',
            'User-Agent': 'Swiggy-Android',
            'Origin': 'https://www.swiggy.com',
            'Referer': 'https://www.swiggy.com/my-account',
            'Cookie': serializeCookieMap(cookieMap)
          },
          body: JSON.stringify(csrf ? { _csrf: csrf } : {}),
          signal: AbortSignal.timeout(3000)
        }).catch(() => {});
      }
    } catch (e) {}
  }

  return true;
}
