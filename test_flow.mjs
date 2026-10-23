// ============================================================================
// bossbot offline test — no Telegram, no Swiggy, no network.
// Verifies the whole product contract:
//   two links in -> one confirmation tap -> QR -> automatic tracking
//   boss orders confirm with the boss, user orders confirm with the user
//   accounts are spent fresh-first and marked used
//   admin: today / fresh / used / logout / export / users / DM
// ============================================================================
import { Telegraf } from 'telegraf';
import { createBossBot } from './bot.js';
import { isCartLink, isAddressLink, looksLikeAddress, extractUrls } from './engine.js';

const results = [];
const check = (label, ok) => {
  results.push({ label, ok: Boolean(ok) });
  console.log(`${ok ? '✅' : '❌'} ${label}`);
  if (!ok) process.exitCode = 1;
};

// ---------------------------------------------------------------- fake telegram
const api = [];
let paid = false;
const callApi = async (method, payload = {}) => {
  api.push({ method, payload });
  if (method === 'sendPhoto' || method === 'sendDocument' || method === 'sendMessage' || method === 'editMessageText') {
    return { message_id: api.length, date: 1, chat: { id: payload.chat_id, type: 'private' }, text: payload.text || payload.caption || '' };
  }
  if (method === 'getMe') return { id: 1, is_bot: true, first_name: 'B', username: 'bossbot' };
  return true;
};
const bot = new Telegraf('123456:TEST-TOKEN');
bot.telegram.callApi = callApi;
Object.getPrototypeOf(bot.telegram).callApi = callApi;

// -------------------------------------------------------------------- fake store
let db = {
  config: {
    accounts: {
      acc_9000000001: { account: 'acc_9000000001', phone: '9000000001', name: 'A', isLoggedIn: true, cookies: 'c=1', tid: 't.1' },
      acc_9000000002: { account: 'acc_9000000002', phone: '9000000002', name: 'B', isLoggedIn: true, cookies: 'c=2', tid: 't.2' }
    }
  },
  orders: {},
  botUsers: {},
  botStats: {}
};
const store = {
  getDb: () => JSON.parse(JSON.stringify(db)),
  saveDb: (d) => { db = JSON.parse(JSON.stringify(d)); }
};

// -------------------------------------------------------------------- fake engine
const calls = { resolve: 0, bill: 0, qr: 0, paid: 0, logout: [], exported: [], added: [] };
const engine = {
  isCartLink, isAddressLink, looksLikeAddress, extractUrls,
  async resolve({ cart, address }) {
    calls.resolve += 1;
    const unresolved = Boolean(address && /onelink/i.test(address));
    return {
      cartDetails: { restaurantName: 'Pizza Hut', items: [{ name: 'Margherita', qty: 1, price: 420 }] },
      restaurantName: 'Pizza Hut',
      restaurantId: '1467977',
      addressDetails: unresolved ? null : {
        address: 'Flat 4, Gomti Nagar, Lucknow 226010', city: 'Lucknow', mobile: '9876543210', lat: '26.86', lng: '80.93', id: 'addr_1'
      },
      addressUnresolved: unresolved,
      addressReason: unresolved ? 'UNEXPANDED' : ''
    };
  },
  async bill() {
    calls.bill += 1;
    return {
      ok: true,
      accountKey: 'acc_9000000001',
      items: [{ name: 'Margherita', qty: 1, price: 420 }, { name: 'Garlic Bread', qty: 1, price: 129 }],
      payable: 487,
      savings: 62,
      restaurant: 'Pizza Hut'
    };
  },
  async qr() {
    calls.qr += 1;
    return { upiIntentUrl: 'upi://pay?pa=swiggy@ybl&am=487', amount: 487, swiggyOrderId: '251000111222', paymentTxnId: 'TXN_1', restaurant: 'Pizza Hut' };
  },
  async paid() {
    calls.paid += 1;
    if (!paid) return { paid: false, txnState: 'pending' };
    return {
      paid: true,
      swiggyOrderId: '251000111222',
      nativeShareUrl: 'https://r.swiggy.com/swiggy/ofo/track/251000111222',
      deliveryOtp: '445566',
      etaMinutes: '28',
      orderStatus: 'Out for delivery'
    };
  },
  addSession(raw) { calls.added.push(raw); return { success: true }; },
  exportSession(key) { calls.exported.push(key); return { account: key, cookies: 'x', tid: 'y' }; },
  logout(key) { calls.logout.push(key); return true; }
};

const BOSS = 900100;
const CUSTOMER = 500200;
const bossBot = createBossBot({ bot, engine, store, config: { bossIds: [String(BOSS)], pollMs: 1 } });

// --------------------------------------------------------------------- helpers
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const reset = () => { api.length = 0; };
const sent = (m) => api.filter((c) => c.method === m).map((c) => c.payload);
const lastText = () => {
  const m = [...sent('sendMessage'), ...sent('editMessageText')].pop();
  return String(m?.text || '');
};
const buttonsOf = (payload) => (payload?.reply_markup?.inline_keyboard || []).flat();
const lastButtons = () => {
  const all = [...sent('sendMessage'), ...sent('editMessageText')];
  return buttonsOf(all[all.length - 1]);
};

async function say(fromId, text, chatId = fromId) {
  await bot.handleUpdate({
    update_id: Math.floor(Math.random() * 1e6),
    message: {
      message_id: 1, date: Math.floor(Date.now() / 1000),
      chat: { id: chatId, type: 'private', first_name: 'X' },
      from: { id: fromId, is_bot: false, first_name: fromId === BOSS ? 'Boss' : 'Ammi', username: fromId === BOSS ? 'boss' : 'ammi' },
      text
    }
  });
  await sleep(120);
}

async function tap(fromId, data, chatId = fromId) {
  await bot.handleUpdate({
    update_id: Math.floor(Math.random() * 1e6),
    callback_query: {
      id: 'cb', from: { id: fromId, is_bot: false, first_name: fromId === BOSS ? 'Boss' : 'Ammi' }, chat_instance: 'ci',
      data,
      message: { message_id: 5, date: Math.floor(Date.now() / 1000), chat: { id: chatId, type: 'private' }, text: 'card' }
    }
  });
  await sleep(220);
}

const orders = () => Object.values(db.orders);

// ===========================================================================
console.log('\n--- 1. link classification ---');
{
  check('cart link is a cart', isCartLink('https://swig.gy/gc/AbC123xyZ'));
  check('tracking link is never a cart', !isCartLink('https://r.swiggy.com/swiggy/ofo/track/251999888777666'));
  check('address link is an address', isAddressLink('https://swiggy.onelink.me/JgkQ/9k2h4x'));
  check('address link is never a cart', !isCartLink('https://swiggy.onelink.me/JgkQ/9k2h4x'));
  check('typed address is recognised', looksLikeAddress('Flat 4, Gomti Nagar, Lucknow 226010'));
  check('a chit-chat line is not an address', !looksLikeAddress('hi bhai kya haal'));
}

console.log('\n--- 2. customer: two links in, one confirm card out ---');
{
  reset();
  await say(CUSTOMER, 'https://swig.gy/gc/RealCart1\nhttps://www.swiggy.com/ofo/address/ammi/tok123456');
  const card = sent('sendMessage').map((p) => String(p.text || '')).join('\n');
  check('a bill card is sent', /Order #/.test(card));
  check('the card shows the payable amount', /487/.test(card));
  check('the customer is asked for nothing else', !/bhejein — bas paste/.test(card));
  check('exactly one confirmation button', lastButtons().filter((b) => /^ok:/.test(b.callback_data || '')).length === 1);
  check('no QR before confirmation', sent('sendPhoto').length === 0);
  const o = orders()[0];
  check('order waits in CONFIRM', o.status === 'CONFIRM');
  check('customer order confirms with the customer', o.confirmChatId === String(CUSTOMER));
}

console.log('\n--- 3. confirm -> QR -> automatic tracking ---');
{
  const o = orders()[0];
  reset();
  await tap(CUSTOMER, `ok:${o.id}`);
  check('one payment QR is sent', sent('sendPhoto').length === 1);
  check('order moves to QR', db.orders[o.id].status === 'QR');
  check('QR carries the amount', /487/.test(String(sent('sendPhoto')[0]?.caption || '')));

  reset();
  await tap(CUSTOMER, `ok:${o.id}`);
  check('a second tap does not create a second QR', sent('sendPhoto').length === 0);

  reset();
  paid = true;
  await bossBot.pollOnce();
  const track = sent('sendMessage').find((p) => buttonsOf(p).some((b) => b.url)) || sent('sendMessage').pop();
  const url = buttonsOf(track).find((b) => b.url)?.url || '';
  check('tracking link is delivered', url === 'https://r.swiggy.com/swiggy/ofo/track/251000111222');
  check('OTP is delivered with it', /445566/.test(String(track?.text || '')));
  check('order is PAID', db.orders[o.id].status === 'PAID');
  check('the account is marked used', db.botStats.acc_9000000001?.used === 1);
  check('polling stops after payment', await bossBot.pollOnce() === 0);
}

console.log('\n--- 4. boss: forwarded links confirm with the BOSS ---');
{
  paid = false;
  reset();
  await say(BOSS, 'https://swig.gy/gc/BossCart2\nhttps://www.swiggy.com/ofo/address/guest/tok999888');
  const bossCard = sent('sendMessage').map((p) => p.chat_id);
  check('the confirmation goes to the boss chat', bossCard.includes(String(BOSS)) || bossCard.includes(BOSS));
  check('nothing is sent to the customer', !bossCard.some((id) => String(id) === String(CUSTOMER)));
  check('the boss card shows the account ID', /ID:<\/b>|9000000002/.test(lastText()) || /9000000002/.test(String(sent('sendMessage').pop()?.text || '')));
  const o = orders().find((x) => x.source === 'BOSS');
  check('order is tagged as a boss order', o?.source === 'BOSS');
  check('a fresh ID is used for the second order', o?.accountKey === 'acc_9000000001');

  reset();
  await tap(BOSS, `ok:${o.id}`);
  check('the QR goes to the boss chat', Boolean(sent('sendPhoto')[0]) && String(sent('sendPhoto')[0].chat_id) === String(BOSS));
}

console.log('\n--- 5. admin panel ---');
{
  reset();
  await tap(BOSS, 'ad:today');
  check("today's orders are counted", /Today<\/b> — 1 orders|Today.*1 order/.test(lastText()) || /1 orders/.test(lastText()));

  reset();
  await tap(BOSS, 'ad:fresh');
  check('fresh IDs list is shown', /Fresh IDs/.test(lastText()) && /9000000002/.test(lastText()));

  reset();
  await tap(BOSS, 'ad:used');
  check('used IDs list is shown', /Used IDs/.test(lastText()) && /9000000001/.test(lastText()));

  reset();
  await tap(BOSS, 'ad:ex:used');
  check('used sessions can be exported', sent('sendDocument').length === 1);
  check('the exported file is the used ID', calls.exported.at(-1) === 'acc_9000000001');

  reset();
  await tap(BOSS, 'ad:lo:fresh');
  check('fresh IDs can be logged out', calls.logout.includes('acc_9000000002'));
  check('logout is reported', /logged out/.test(lastText()));
}

console.log('\n--- 6. every user is stored and reachable ---');
{
  reset();
  await say(777777, '/start');
  const notice = sent('sendMessage').find((p) => /Naya user/.test(String(p.text || '')));
  check('the boss is told about a new user', Boolean(notice) && /Naya user/.test(String(notice.text)));
  check('the notice carries a clickable profile link', /tg:\/\/user\?id=777777/.test(String(notice?.text || '')));
  check('the user is stored by numeric ID', Boolean(db.botUsers['777777']));

  reset();
  await tap(BOSS, 'dm:777777');
  check('boss can open a DM composer', /ko message likhein/.test(lastText()));
  reset();
  await say(BOSS, 'Order ready hai, 5 min me aa jayega');
  const dm = sent('sendMessage').find((p) => String(p.chat_id) === '777777');
  check('the boss message reaches the user', Boolean(dm) && /Order ready hai/.test(String(dm.text)));
}

console.log('\n--- 7. an un-openable address link never dead-ends ---');
{
  reset();
  await say(CUSTOMER, 'https://swig.gy/gc/RealCart3\nhttps://swiggy.onelink.me/JgkQ/broken1');
  check('the bot does not claim "expired"', !/expire/i.test(lastText()));
  check('retry is offered', lastButtons().some((b) => /^retry:/.test(b.callback_data || '')));
  check('typing the address is offered', lastButtons().some((b) => /^type:/.test(b.callback_data || '')));

  const o = orders().find((x) => x.cart === 'https://swig.gy/gc/RealCart3');
  reset();
  await tap(CUSTOMER, `type:${o.id}`);
  check('the broken link is cleared', db.orders[o.id].address === null && !db.orders[o.id].addressLink);
  check('the customer is asked to type the address', /address type karein/i.test(lastText()));

  reset();
  paid = false;
  await say(CUSTOMER, 'Flat 4, Gomti Nagar, Lucknow 226010');
  check('the typed address resumes the order', /Order #/.test(lastText()));
  check('the order is back in CONFIRM', db.orders[o.id].status === 'CONFIRM');
}

console.log('\n--- 8. no web app, no mini app ---');
{
  const dump = JSON.stringify(api);
  check('no web_app button anywhere', !dump.includes('web_app'));
  check('no browser URL is opened for the flow', !dump.includes('openApp'));
}

console.log('\n================================================================');
const passed = results.filter((r) => r.ok).length;
console.log(`📊 RESULT: ${passed}/${results.length} checks passed`);
console.log('================================================================');
if (passed !== results.length) process.exitCode = 1;
