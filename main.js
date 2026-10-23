// ============================================================================
// main.js — boot. Nothing else.
// ============================================================================
import 'dotenv/config';
import http from 'node:http';
import { Telegraf } from 'telegraf';
import { createBossBot } from './bot.js';
import { createEngine } from './engine.js';
import { getDb, saveDb } from './vendor/store.js';

const TOKEN = process.env.BOT_TOKEN;
if (!TOKEN) {
  console.error('× BOT_TOKEN missing. Set it in the environment.');
  process.exit(1);
}

const bossIds = String(process.env.BOSS_IDS || process.env.BOSS_ID || '')
  .split(/[,;\s]+/).map((s) => s.trim()).filter(Boolean);
if (!bossIds.length) {
  console.error('× BOSS_IDS missing — the boss Telegram numeric ID is required.');
  process.exit(1);
}

const bot = new Telegraf(TOKEN, { handlerTimeout: 180_000 });
const engine = createEngine();
const bossBot = createBossBot({
  bot,
  engine,
  store: { getDb, saveDb },
  config: { bossIds, pollMs: Number(process.env.POLL_MS || 15000) }
});

// Health endpoint (Render) — also proves the process is alive.
const port = Number(process.env.PORT || 0);
if (port > 0) {
  http.createServer((_req, res) => {
    const orders = Object.values(getDb().orders || {});
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({
      status: 'ok',
      orders: orders.length,
      paid: orders.filter((o) => o.status === 'PAID').length,
      accounts: Object.keys(getDb().config?.accounts || {}).length,
      at: new Date().toISOString()
    }));
  }).listen(port, '0.0.0.0', () => console.log(`◎ health on 0.0.0.0:${port}`));
}

const ticker = bossBot.startTicker();

// A bad token / network blip must not surface as a raw stack trace: log one
// clear line and exit non-zero so the host restarts the container.
try {
  await bot.launch({ dropPendingUpdates: true });
  console.log(`⚙ bossbot live — boss ${bossIds.join(', ')}`);
} catch (err) {
  console.error('× Telegram launch failed:', err?.description || err?.message || err);
  clearInterval(ticker);
  process.exit(1);
}

for (const sig of ['SIGINT', 'SIGTERM']) {
  process.once(sig, () => {
    clearInterval(ticker);
    try { bot.stop(sig); } catch {}
  });
}
