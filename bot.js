// ============================================================================
// bossbot — two ways in, one tap, everything else automatic.
// ----------------------------------------------------------------------------
//  1. BOSS mode  : boss sends/forwards the links   -> boss confirms -> QR + tracking
//  2. USER mode  : anyone sends the links          -> user confirms -> QR + tracking
//
// No web app, no mini app, no dashboard: the whole product is this chat.
// ============================================================================

import { Markup } from 'telegraf';
import QRCode from 'qrcode';

const esc = (v) => String(v ?? '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
const money = (v) => `₹${Number(v || 0).toFixed(0)}`;
const NOW = () => Date.now();
const newId = () => `O${NOW().toString(36).toUpperCase().slice(-6)}${Math.random().toString(36).slice(2, 4).toUpperCase()}`;
const todayKey = (t = Date.now()) => new Date(t).toLocaleDateString('en-CA', { timeZone: 'Asia/Kolkata' });

const ACTIVE = ['DRAFT', 'BILLING', 'CONFIRM', 'QR'];

export function createBossBot({ bot, engine, store, config = {} }) {
  const bossIds = new Set((config.bossIds || []).map(String));
  const pollMs = config.pollMs ?? 15000;
  const qrTtlMs = config.qrTtlMs ?? 15 * 60 * 1000;
  const waitingDm = new Map(); // bossId -> targetUserId

  const isBoss = (id) => bossIds.has(String(id));
  const db = () => store.getDb();
  const save = (d) => store.saveDb(d);

  // ------------------------------------------------------------------ accounts
  function stats() {
    const d = db();
    if (!d.botStats) d.botStats = {};
    return d.botStats;
  }

  function accountRows() {
    const d = db();
    const s = stats();
    return Object.entries(d.config?.accounts || {})
      .filter(([, a]) => a && typeof a === 'object')
      .map(([key, a]) => ({
        key,
        phone: String(a.phone || a.mobile || key.replace(/^acc_/, '')),
        name: String(a.name || a.swiggyName || ''),
        live: Boolean(a.isLoggedIn && !a.isLoggedOut && (a.cookies || a.tid || a.token)),
        used: Number(s[key]?.used || 0),
        lastUsedAt: s[key]?.lastUsedAt || null
      }))
      .sort((a, b) => b.used - a.used || a.phone.localeCompare(b.phone));
  }

  const freshRows = () => accountRows().filter((r) => r.live && r.used === 0);
  const usedRows = () => accountRows().filter((r) => r.live && r.used > 0);

  /** Least-used live account wins, so every fresh ID is spent before an old one. */
  function pickAccount() {
    const pool = accountRows().filter((r) => r.live);
    if (!pool.length) return null;
    pool.sort((a, b) => a.used - b.used || String(a.lastUsedAt || '').localeCompare(String(b.lastUsedAt || '')));
    return pool[0];
  }

  function markUsed(key) {
    const s = stats();
    const rec = s[key] || { used: 0, firstUsedAt: null, lastUsedAt: null };
    rec.used = Number(rec.used || 0) + 1;
    rec.firstUsedAt = rec.firstUsedAt || new Date().toISOString();
    rec.lastUsedAt = new Date().toISOString();
    s[key] = rec;
    const d = db();
    d.botStats = s;
    save(d);
  }

  // --------------------------------------------------------------------- users
  function trackUser(from) {
    if (!from?.id || isBoss(from.id)) return { isNew: false };
    const d = db();
    if (!d.botUsers) d.botUsers = {};
    const id = String(from.id);
    const prev = d.botUsers[id];
    d.botUsers[id] = {
      id,
      name: [from.first_name, from.last_name].filter(Boolean).join(' ') || prev?.name || 'User',
      username: from.username || prev?.username || '',
      firstSeen: prev?.firstSeen || new Date().toISOString(),
      lastSeen: new Date().toISOString(),
      orders: Number(prev?.orders || 0)
    };
    save(d);
    return { isNew: !prev, user: d.botUsers[id] };
  }

  async function touchUser(from) {
    const res = trackUser(from);
    if (res.isNew && res.user) {
      await notifyBoss(`🆕 <b>Naya user</b>\n👤 ${userLine(res.user)}\n<i>Naam dabakar profile kholein, ya niche se message karein.</i>`,
        Markup.inlineKeyboard([[{ text: `💬 Message ${res.user.name}`, callback_data: `dm:${res.user.id}` }]]));
    }
    return res;
  }

  const userLink = (u) => `<a href="tg://user?id=${esc(u.id)}">${esc(u.name || 'User')}</a>`;
  const userLine = (u) => `${userLink(u)} <code>${esc(u.id)}</code>${u.username ? ` @${esc(u.username)}` : ''}`;

  async function notifyBoss(text, extra = {}) {
    for (const id of bossIds) {
      await bot.telegram.sendMessage(id, text, { parse_mode: 'HTML', link_preview_options: { is_disabled: true }, ...extra }).catch(() => {});
    }
  }

  // -------------------------------------------------------------------- orders
  function liveOrderFor(chatId) {
    return Object.values(db().orders || {})
      .filter((o) => o && String(o.confirmChatId) === String(chatId) && ACTIVE.includes(o.status))
      .sort((a, b) => (b.createdAt || '').localeCompare(a.createdAt || ''))[0];
  }

  function createOrder({ from, chatId, source }) {
    const d = db();
    if (!d.orders) d.orders = {};
    const order = {
      id: newId(),
      source,
      userId: String(from.id),
      userName: [from.first_name, from.last_name].filter(Boolean).join(' ') || 'User',
      confirmChatId: String(chatId),
      payerChatId: String(chatId),
      status: 'DRAFT',
      createdAt: new Date().toISOString(),
      cart: null,
      address: null,
      addressDetails: null,
      addressUnresolved: false
    };
    d.orders[order.id] = order;
    save(d);
    return order;
  }

  function updateOrder(id, patch) {
    const d = db();
    const o = d.orders?.[id];
    if (!o) return null;
    Object.assign(o, patch);
    save(d);
    return o;
  }

  /** The one automatic pipeline: links in -> bill -> confirm card out. */
  async function startBilling(orderId, chatId, { notice } = {}) {
    updateOrder(orderId, { status: 'BILLING' });
    const order = db().orders[orderId];
    await bot.telegram.sendMessage(chatId, notice || '⏳ <b>Best price nikal raha hoon…</b>', { parse_mode: 'HTML' }).catch(() => {});

    let meta;
    try {
      meta = await engine.resolve({ cart: order.cart, address: order.address });
    } catch (e) {
      meta = { addressUnresolved: false };
    }
    const addressDetails = meta.addressDetails || order.addressDetails || null;
    const typedOnly = Boolean(order.addressTyped) && !order.addressLink;
    updateOrder(orderId, {
      cartDetails: meta.cartDetails || order.cartDetails || null,
      restaurantName: meta.restaurantName || order.restaurantName || '',
      restaurantId: meta.restaurantId || null,
      groupCartId: meta.groupCartId || null,
      hostName: meta.hostName || null,
      addressDetails,
      addressUnresolved: Boolean(meta.addressUnresolved) && !typedOnly,
      addressReason: meta.addressReason || ''
    });

    // A link we could not open is never allowed to dead-end the order.
    if (meta.addressUnresolved && !typedOnly && !addressDetails) {
      updateOrder(orderId, { status: 'DRAFT' });
      return bot.telegram.sendMessage(chatId,
        `⏳ <b>Swiggy ka address link khul nahi paya</b>\n\n` +
        `<i>Link saved hai. Retry karein, ya seedha address type kar dein — order chalega.</i>`,
        {
          parse_mode: 'HTML',
          ...Markup.inlineKeyboard([
            [{ text: '↻ Retry', callback_data: `retry:${orderId}` }],
            [{ text: '✍️ Address type karein', callback_data: `type:${orderId}` }]
          ])
        }).catch(() => {});
    }

    const account = pickAccount();
    if (!account) {
      updateOrder(orderId, { status: 'DRAFT' });
      return bot.telegram.sendMessage(chatId,
        '🔒 <b>Koi Swiggy account ready nahi hai</b>\n\n<i>Boss ko bata diya gaya hai.</i>',
        { parse_mode: 'HTML' }).catch(() => {}).then(() => notifyBoss('⚠️ <b>Account khatam</b> — koi live Swiggy ID nahi bachi. Naya session JSON bhejein.'));
    }

    const bill = await engine.bill({ ...db().orders[orderId], accountHint: account.key });
    if (!bill.ok) {
      updateOrder(orderId, { status: 'DRAFT', error: bill.error });
      return bot.telegram.sendMessage(chatId,
        `⚠️ <b>Bill nahi ban paya</b>\n\n<i>${esc(bill.error)}</i>`,
        { parse_mode: 'HTML', ...Markup.inlineKeyboard([[{ text: '↻ Retry', callback_data: `retry:${orderId}` }]]) }).catch(() => {});
    }

    const items = (bill.items || []).slice(0, 12);
    const lines = items.map((it) => `• ${esc(it.name)} ×${esc(it.qty || 1)} — ${money(it.price * (it.qty || 1))}`).join('\n');
    const isBossOrder = isBoss(order.userId);
    const card =
      `🧾 <b>Order #${esc(order.id)}</b>${isBossOrder ? ' <i>(boss)</i>' : ''}\n` +
      `🍽 <b>${esc(bill.restaurant || 'Swiggy')}</b>\n\n` +
      (lines ? `${lines}\n\n` : '') +
      `📍 <b>Address:</b> ${esc(addressDetails?.address || order.address || '—')}\n` +
      (addressDetails?.mobile ? `📞 ${esc(addressDetails.mobile)}\n` : '') +
      `\n💰 <b>Payable: ${money(bill.payable)}</b>` +
      (bill.savings ? ` <i>(save ${money(bill.savings)})</i>` : '') +
      (isBossOrder ? `\n🔑 <b>ID:</b> <code>${esc(account.phone)}</code>` : '') +
      `\n\n${isBossOrder ? 'Confirm karke QR banayein.' : 'Confirm karein — phir QR aa jayega.'}`;

    updateOrder(orderId, {
      status: 'CONFIRM',
      accountKey: bill.accountKey || account.key,
      items: bill.items || [],
      payable: bill.payable,
      savings: bill.savings,
      restaurantName: bill.restaurant || order.restaurantName,
      confirmChatId: order.confirmChatId
    });

    return bot.telegram.sendMessage(order.confirmChatId, card, {
      parse_mode: 'HTML',
      ...Markup.inlineKeyboard([
        [{ text: `✅ Confirm ${money(bill.payable)}`, callback_data: `ok:${orderId}` }],
        [{ text: '✖ Cancel', callback_data: `no:${orderId}` }]
      ])
    }).catch(() => {});
  }

  /** Confirm tap -> real Swiggy payment QR -> automatic payment watching. */
  async function confirmOrder(orderId, chatId) {
    const order = db().orders?.[orderId];
    if (!order) return { ok: false, error: 'Order not found.' };
    if (order.status === 'QR') return { ok: true, already: true };
    if (order.status !== 'CONFIRM') return { ok: false, error: 'This order is not waiting for confirmation.' };

    updateOrder(orderId, { status: 'QR', confirmedAt: new Date().toISOString() });
    let qr;
    try {
      qr = await engine.qr(order.accountKey, db().orders[orderId]);
    } catch (e) {
      updateOrder(orderId, { status: 'CONFIRM', error: e.message });
      return { ok: false, error: e.message };
    }

    const live = db().orders[orderId];
    updateOrder(orderId, {
      status: 'QR',
      swiggyOrderId: qr.swiggyOrderId,
      paymentTxnId: qr.paymentTxnId,
      payable: qr.amount || live.payable,
      qrCreatedAt: NOW(),
      nextPollAt: NOW() + pollMs
    });

    const caption =
      `💳 <b>Payment QR</b> — ${money(qr.amount || live.payable)}\n` +
      `<i>${esc(qr.restaurant || live.restaurantName || 'Swiggy')}</i>\n\n` +
      `Scan karein ya UPI se pay karein.\n` +
      `<i>Payment khud check ho jayega — tracking link yahin aa jayega.</i>`;

    try {
      const png = await QRCode.toBuffer(qr.upiIntentUrl, { width: 512, margin: 1 });
      await bot.telegram.sendPhoto(chatId, { source: png }, { caption, parse_mode: 'HTML' });
    } catch {
      await bot.telegram.sendMessage(chatId, `${caption}\n\n<a href="${esc(qr.upiIntentUrl)}">Pay now</a>`, { parse_mode: 'HTML' }).catch(() => {});
    }
    return { ok: true, qr };
  }

  async function pollOrder(order) {
    const res = await engine.paid(order.accountKey, order).catch((e) => ({ paid: false, error: e.message }));
    const d = db();
    const fresh = d.orders?.[order.id];
    if (!fresh || fresh.status !== 'QR') return;
    if (!res?.paid) {
      updateOrder(order.id, { nextPollAt: NOW() + pollMs, lastPollError: res?.error || res?.txnState || '' });
      if (NOW() - Number(fresh.qrCreatedAt || 0) > qrTtlMs) {
        updateOrder(order.id, { status: 'CONFIRM' });
        await bot.telegram.sendMessage(fresh.payerChatId,
          '⌛ <b>QR expire ho gaya</b>\n\n<i>Confirm dabayein — naya QR ban jayega.</i>',
          { parse_mode: 'HTML', ...Markup.inlineKeyboard([[{ text: '↻ Naya QR', callback_data: `ok:${order.id}` }]]) }).catch(() => {});
      }
      return;
    }

    const tracking = res.nativeShareUrl || res.swiggyWebTrackUrl || '';
    updateOrder(order.id, {
      status: 'PAID',
      paidAt: new Date().toISOString(),
      swiggyOrderId: res.swiggyOrderId || fresh.swiggyOrderId,
      tracking,
      otp: res.deliveryOtp || '',
      eta: res.etaMinutes || '',
      liveStatus: res.orderStatus || ''
    });
    markUsed(fresh.accountKey);

    const lines = [
      `✅ <b>Order confirmed</b> — ${money(fresh.payable)}`,
      `<i>${esc(fresh.restaurantName || 'Swiggy')}</i>`,
      res.swiggyOrderId ? `🆔 <code>${esc(res.swiggyOrderId)}</code>` : '',
      res.etaMinutes ? `⏱ ETA ${esc(res.etaMinutes)} min` : '',
      res.deliveryOtp ? `🔐 OTP <code>${esc(res.deliveryOtp)}</code>` : ''
    ].filter(Boolean).join('\n');

    await bot.telegram.sendMessage(fresh.payerChatId, lines, {
      parse_mode: 'HTML',
      ...(tracking ? Markup.inlineKeyboard([[{ text: '🛵 Track on Swiggy', url: tracking }]]) : {})
    }).catch(() => {});

    if (!isBoss(fresh.userId)) {
      const u = db().botUsers?.[fresh.userId];
      await notifyBoss(
        `📦 <b>User order paid</b> — ${money(fresh.payable)}\n` +
        `👤 ${u ? userLine(u) : esc(fresh.userId)}\n` +
        `🍽 ${esc(fresh.restaurantName || '')}\n` +
        (tracking ? `🛵 ${esc(tracking)}` : '')
      );
    }
  }

  async function pollOnce() {
    const orders = Object.values(db().orders || {})
      .filter((o) => o && o.status === 'QR' && Number(o.nextPollAt || 0) <= NOW());
    for (const o of orders) await pollOrder(o).catch(() => {});
    return orders.length;
  }

  // --------------------------------------------------------------------- admin
  const todayOrders = () => Object.values(db().orders || {})
    .filter((o) => o && o.paidAt && todayKey(new Date(o.paidAt).getTime()) === todayKey(NOW()));

  function adminHome() {
    const todays = todayOrders();
    const total = todays.reduce((s, o) => s + Number(o.payable || 0), 0);
    return {
      text:
        `🛠 <b>Admin</b>\n\n` +
        `📦 Today: <b>${todays.length}</b> orders · <b>${money(total)}</b>\n` +
        `🟢 Fresh IDs: <b>${freshRows().length}</b> · 🔵 Used IDs: <b>${usedRows().length}</b>\n` +
        `👥 Users: <b>${Object.keys(db().botUsers || {}).length}</b>`,
      keyboard: Markup.inlineKeyboard([
        [{ text: '📦 Today', callback_data: 'ad:today' }, { text: '👥 Users', callback_data: 'ad:users' }],
        [{ text: `🟢 Fresh (${freshRows().length})`, callback_data: 'ad:fresh' }, { text: `🔵 Used (${usedRows().length})`, callback_data: 'ad:used' }],
        [{ text: '🚪 Logout fresh', callback_data: 'ad:lo:fresh' }, { text: '🚪 Logout used', callback_data: 'ad:lo:used' }],
        [{ text: '📤 Export fresh', callback_data: 'ad:ex:fresh' }, { text: '📤 Export used', callback_data: 'ad:ex:used' }],
        [{ text: '➕ Add account', callback_data: 'ad:add' }]
      ])
    };
  }

  const idLines = (rows) => rows.length
    ? rows.map((r) => `• <code>${esc(r.phone)}</code>${r.name ? ` ${esc(r.name)}` : ''}${r.used ? ` — ${r.used} order(s)` : ''}`).join('\n')
    : '<i>Koi nahi.</i>';

  async function sendToday(ctx) {
    const todays = todayOrders();
    const byId = {};
    for (const o of todays) byId[o.accountKey] = (byId[o.accountKey] || 0) + 1;
    const lines = todays.length
      ? todays.map((o) => `• <b>${money(o.payable)}</b> — ${esc(o.restaurantName || '')} — <code>${esc(accountPhone(o.accountKey))}</code>`).join('\n')
      : '<i>Aaj koi order nahi.</i>';
    await ctx.reply(
      `📦 <b>Today</b> — ${todays.length} orders · <b>${money(todays.reduce((s, o) => s + Number(o.payable || 0), 0))}</b>\n\n${lines}` +
      (Object.keys(byId).length ? `\n\n🔑 IDs used today: ${Object.keys(byId).map((k) => `<code>${esc(accountPhone(k))}</code>`).join(', ')}` : ''),
      { parse_mode: 'HTML' }
    );
  }

  const accountPhone = (key) => accountRows().find((r) => r.key === key)?.phone || String(key || '—').replace(/^acc_/, '');

  async function sendUsers(ctx) {
    const users = Object.values(db().botUsers || {}).sort((a, b) => (b.lastSeen || '').localeCompare(a.lastSeen || ''));
    if (!users.length) return ctx.reply('👥 <i>Abhi koi user nahi.</i>', { parse_mode: 'HTML' });
    const rows = users.slice(0, 20).map((u) => [Markup.button.callback(`${u.name} · ${u.orders || 0} orders`, `dm:${u.id}`)]);
    await ctx.reply(
      `👥 <b>Users</b> (${users.length})\n\n` + users.slice(0, 20).map(userLine).join('\n'),
      { parse_mode: 'HTML', ...Markup.inlineKeyboard(rows) }
    );
  }

  async function logoutGroup(ctx, group) {
    const rows = group === 'fresh' ? freshRows() : usedRows();
    if (!rows.length) return ctx.reply('<i>Koi ID nahi.</i>', { parse_mode: 'HTML' });
    let done = 0;
    for (const r of rows) {
      try { engine.logout(r.key); done += 1; } catch {}
    }
    await ctx.reply(`🚪 <b>${done} ${group} ID logged out</b>\n<i>${rows.map((r) => r.phone).join(', ')}</i>`, { parse_mode: 'HTML' });
  }

  async function exportGroup(ctx, group) {
    const rows = group === 'fresh' ? freshRows() : usedRows();
    if (!rows.length) return ctx.reply('<i>Koi ID nahi.</i>', { parse_mode: 'HTML' });
    let sent = 0;
    for (const r of rows) {
      const json = engine.exportSession(r.key);
      if (!json) continue;
      await ctx.replyWithDocument(
        { source: Buffer.from(JSON.stringify(json, null, 2)), filename: `swiggy-${group}-${r.phone}.json` },
        { caption: `${group} · ${r.phone}` }
      ).catch(() => {});
      sent += 1;
    }
    await ctx.reply(`📤 <b>${sent} ${group} JSON bheje</b>`, { parse_mode: 'HTML' });
  }

  async function addAccount(ctx, raw) {
    const res = await Promise.resolve(engine.addSession(raw)).catch((e) => ({ success: false, error: e.message }));
    if (res?.success === false) return ctx.reply(`⚠️ <b>Import fail</b>\n<i>${esc(res.error || 'Invalid session JSON')}</i>`, { parse_mode: 'HTML' });
    await ctx.reply(`✅ <b>Account added</b>\n<i>Fresh list me aa gaya.</i>`, { parse_mode: 'HTML' });
  }

  // -------------------------------------------------------------------- intake
  async function handleIntake(ctx, text) {
    const from = ctx.from;
    const chatId = String(ctx.chat.id);
    const bossOrder = isBoss(from.id);
    const urls = engine.extractUrls(text);
    const cart = urls.find((u) => engine.isCartLink(u)) || null;
    const addressLink = urls.find((u) => engine.isAddressLink(u)) || null;
    const typedAddress = !addressLink && engine.looksLikeAddress(text) ? text.trim() : null;

    // Reuse the draft this chat is still filling; anything already confirmed is a
    // finished thought, so a new message starts a new order.
    let order = liveOrderFor(chatId);
    if (order && order.status !== 'DRAFT') order = null;
    if (!order) order = createOrder({ from, chatId, source: bossOrder ? 'BOSS' : 'USER' });

    const d = db();
    const cur = d.orders[order.id];
    const patch = {};
    if (cart) patch.cart = cart;
    if (addressLink) Object.assign(patch, { address: addressLink, addressLink, addressTyped: false });
    if (typedAddress) Object.assign(patch, { address: typedAddress, addressLink: null, addressTyped: true });
    Object.assign(cur, patch);
    save(d);

    const missing = [];
    if (!cur.cart) missing.push('cart link');
    if (!cur.address) missing.push('address link (ya seedha address)');
    if (missing.length) {
      return ctx.reply(
        `🛒 <b>${bossOrder ? 'Boss order' : 'Order'}</b>\n\n` +
        `✅ ${cur.cart ? 'Cart' : '—'} · ${cur.address ? 'Address' : '—'}\n\n` +
        `Ab <b>${missing.join(' + ')}</b> bhejein — bas paste, kuch type nahi.`,
        { parse_mode: 'HTML' }
      );
    }
    return startBilling(order.id, chatId);
  }

  // ------------------------------------------------------------------ handlers
  bot.start(async (ctx) => {
    await touchUser(ctx.from);
    await ctx.reply(
      `👋 <b>Namaste ${esc(ctx.from.first_name || '')}</b>\n\n` +
      `🛒 Cart link + 📍 Address bhejein.\n` +
      `<i>Bas do link — baaki sab automatic.</i>`,
      { parse_mode: 'HTML' }
    );
    if (isBoss(ctx.from.id)) await ctx.reply(adminHome().text, { parse_mode: 'HTML', ...adminHome().keyboard });
  });

  bot.command('admin', async (ctx) => {
    if (!isBoss(ctx.from.id)) return;
    const home = adminHome();
    await ctx.reply(home.text, { parse_mode: 'HTML', ...home.keyboard });
  });

  bot.on('text', async (ctx) => {
    const from = ctx.from;
    const text = String(ctx.message.text || '').trim();
    const boss = isBoss(from.id);
    await touchUser(from);

    // boss is answering "message this user"
    if (boss && waitingDm.has(String(from.id))) {
      const target = waitingDm.get(String(from.id));
      waitingDm.delete(String(from.id));
      await bot.telegram.sendMessage(target, `💬 <b>Boss:</b>\n${esc(text)}`, { parse_mode: 'HTML' }).catch(() => {});
      return ctx.reply(`✅ Message bhej diya <code>${esc(target)}</code> se.`, { parse_mode: 'HTML' });
    }

    // boss pastes a session JSON
    if (boss && /"cookies"\s*:/.test(text)) return addAccount(ctx, text);

    // bare "fresh"/"used" shortcuts for the boss
    if (boss && /^\/(fresh|used)$/i.test(text)) {
      const group = text.slice(1).toLowerCase();
      const rows = group === 'fresh' ? freshRows() : usedRows();
      return ctx.reply(`<b>${group}</b>\n${idLines(rows)}`, { parse_mode: 'HTML' });
    }

    if (text.startsWith('/')) return;

    const hasInput = engine.extractUrls(text).length > 0 || engine.looksLikeAddress(text);
    if (!hasInput) {
      return ctx.reply('🛒 Cart link + 📍 address bhejein — bas do link.', { parse_mode: 'HTML' });
    }
    return handleIntake(ctx, text);
  });

  bot.on('document', async (ctx) => {
    if (!isBoss(ctx.from.id)) return;
    const doc = ctx.message.document;
    if (!/\.json$/i.test(doc.file_name || '')) return ctx.reply('Sirf <code>.json</code> session file.', { parse_mode: 'HTML' });
    const link = await ctx.telegram.getFileLink(doc.file_id).catch(() => null);
    if (!link) return ctx.reply('File download nahi hui.');
    const raw = await (await fetch(String(link))).text().catch(() => '');
    return addAccount(ctx, raw);
  });

  bot.action('new', async (ctx) => {
    await ctx.answerCbQuery().catch(() => {});
    const d = db();
    const cur = liveOrderFor(ctx.chat.id);
    if (cur && cur.status === 'DRAFT') {
      delete d.orders[cur.id];
      save(d);
    }
    await ctx.reply('🛒 Cart link + 📍 address bhejein.');
  });

  bot.action(/^ok:(.+)$/, async (ctx) => {
    const orderId = ctx.match[1];
    const order = db().orders?.[orderId];
    if (!order) return ctx.answerCbQuery('Order not found.').catch(() => {});
    if (String(ctx.from.id) !== String(order.confirmChatId)) {
      return ctx.answerCbQuery('Ye order aapka nahi hai.', { show_alert: true }).catch(() => {});
    }
    await ctx.answerCbQuery('QR ban raha hai…').catch(() => {});
    const res = await confirmOrder(orderId, String(ctx.chat.id));
    if (!res.ok) await ctx.reply(`⚠️ ${esc(res.error)}`, { parse_mode: 'HTML' });
  });

  bot.action(/^no:(.+)$/, async (ctx) => {
    await ctx.answerCbQuery('Cancelled').catch(() => {});
    const orderId = ctx.match[1];
    const order = db().orders?.[orderId];
    if (order && String(ctx.from.id) === String(order.confirmChatId)) updateOrder(orderId, { status: 'CANCELLED' });
  });

  bot.action(/^retry:(.+)$/, async (ctx) => {
    await ctx.answerCbQuery('Dobara…').catch(() => {});
    const orderId = ctx.match[1];
    if (db().orders?.[orderId]) return startBilling(orderId, String(ctx.chat.id), { notice: '↻ <b>Dobara try…</b>' });
  });

  bot.action(/^type:(.+)$/, async (ctx) => {
    await ctx.answerCbQuery().catch(() => {});
    const orderId = ctx.match[1];
    const d = db();
    const o = d.orders?.[orderId];
    if (!o) return;
    Object.assign(o, { address: null, addressLink: null, addressTyped: true, addressDetails: null, addressUnresolved: false, status: 'DRAFT' });
    save(d);
    await ctx.reply('✍️ Poora address type karein (flat, area, landmark, city).');
  });

  bot.action(/^ad:([a-z]+)(?::([a-z]+))?$/, async (ctx) => {
    if (!isBoss(ctx.from.id)) return ctx.answerCbQuery('Unauthorized').catch(() => {});
    await ctx.answerCbQuery().catch(() => {});
    const [, what, sub] = ctx.match;
    if (what === 'today') return sendToday(ctx);
    if (what === 'users') return sendUsers(ctx);
    if (what === 'fresh') return ctx.reply(`🟢 <b>Fresh IDs (${freshRows().length})</b>\n\n${idLines(freshRows())}`, { parse_mode: 'HTML' });
    if (what === 'used') return ctx.reply(`🔵 <b>Used IDs (${usedRows().length})</b>\n\n${idLines(usedRows())}`, { parse_mode: 'HTML' });
    if (what === 'lo') return logoutGroup(ctx, sub);
    if (what === 'ex') return exportGroup(ctx, sub);
    if (what === 'add') return ctx.reply('➕ Session JSON paste karein, ya <code>.json</code> file bhejein.', { parse_mode: 'HTML' });
  });

  bot.action(/^dm:(.+)$/, async (ctx) => {
    if (!isBoss(ctx.from.id)) return ctx.answerCbQuery('Unauthorized').catch(() => {});
    await ctx.answerCbQuery().catch(() => {});
    const target = String(ctx.match[1]);
    const u = db().botUsers?.[target];
    if (!u) return ctx.reply('User not found.');
    waitingDm.set(String(ctx.from.id), target);
    await ctx.reply(
      `💬 <b>${esc(u.name)}</b> ko message likhein.\n👤 ${userLink(u)} · <code>${esc(target)}</code>`,
      { parse_mode: 'HTML', reply_markup: { force_reply: true, selective: true, input_field_placeholder: 'Message…' } }
    );
  });

  return {
    pollOnce,
    startTicker: (ms = pollMs) => setInterval(() => pollOnce().catch(() => {}), ms),
    adminHome,
    _internals: { pickAccount, markUsed, freshRows, usedRows, todayOrders, confirmOrder, handleIntake, startBilling, accountRows }
  };
}
