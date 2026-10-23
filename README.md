# bossbot

Two Swiggy links in → one tap → tracking link out. No web app, no dashboard:
the whole product is a Telegram chat.

Built as a fresh, deliberately short layer on top of the proven Swiggy engine
(`vendor/`, copied from the parent project). All the new logic lives in three
files: `bot.js`, `engine.js`, `main.js`.

```
bossbot/
├── bot.js        the entire product: intake, confirm, QR, tracking, admin
├── engine.js     the only file that talks to vendor/ (Swiggy)
├── main.js       boot (env, health, launch)
├── test_flow.mjs 49 offline checks — no Telegram, no Swiggy, no network
└── vendor/       copied Swiggy engine (untouched, proven in production)
```

## Two ways in

| Who sends the links | Who confirms | Where the QR goes |
|---|---|---|
| **Boss** (sends or forwards) | **Boss** | Boss chat |
| **A user** | **That user** | That user's chat |

Nothing else is asked. Cart + address in one message → zero questions. Only one
link → one short line asking for the other. After the tap, everything is
automatic: account pick → live bill → QR → payment watch → tracking link.

## The flow

```
cart link + address link
        │
        ▼
 resolve links ──► pick freshest Swiggy ID ──► live bill
        │                                       │
        │                                       ▼
        │                          one confirmation card + 1 button
        │                                       │
        │                            (boss or user taps)
        │                                       ▼
        │                          real Swiggy payment QR
        │                                       │
        └──────────── poll every 15s ───────────┘
                                                │ paid
                                                ▼
                          ✅ tracking link + OTP + ETA in the same chat
                          the Swiggy ID is marked USED
```

If an address link cannot be opened, the bot says exactly that (never "expired"
unless Swiggy really rejected the token) and offers **Retry** or **type the
address** — the order always has a way forward.

## Admin (boss only)

`/admin` or the panel button at `/start`:

| Button | What it does |
|---|---|
| 📦 Today | today's order count, ₹ total, which IDs were used |
| 🟢 Fresh / 🔵 Used | list of unused / already-used Swiggy IDs |
| 🚪 Logout fresh / used | purges those sessions from the vault |
| 📤 Export fresh / used | sends each session back as a `.json` file |
| 👥 Users | everyone who ever used the bot |
| ➕ Add account | paste a session JSON, or send a `.json` file |

**Every user is stored by numeric Telegram ID** (never username) and shown as a
clickable `<a href="tg://user?id=…">` link that opens their profile. The boss is
notified the moment someone new talks to the bot, and can message any user
directly from the bot (`👥 Users` → tap a name → type).

## Accounts: fresh first

`botStats[key].used` counts how many orders each Swiggy ID has placed. The
picker always takes the **least-used** live account, so a brand-new ID is spent
before an old one is touched again. "Fresh" = 0 orders, "Used" = 1+.

## Run locally

```bash
cd bossbot
npm install --omit=dev --ignore-scripts
cp .env.example .env      # fill BOT_TOKEN + BOSS_IDS
npm start
npm test                  # 49 offline checks
```

## Deploy (Render)

`render.yaml` in this folder is ready — set the repo **root directory** to
`bossbot`, then add:

| Env var | Required | Notes |
|---|---|---|
| `BOT_TOKEN` | yes | from @BotFather |
| `BOSS_IDS` | yes | comma-separated numeric Telegram IDs |
| `PORT` | auto | Render sets it; `/` returns a small JSON health blob |
| `POLL_MS` | no | payment poll interval, default `15000` |

Add a **persistent disk** mounted at `vendor/data` so sessions and orders
survive redeploys.

## What the offline tests cover (49 checks)

link classification · customer flow end-to-end · single QR on double tap ·
automatic tracking + OTP · account marked used · boss confirms with the boss ·
fresh-first account picking · today/fresh/used lists · logout fresh ·
export used · new-user notification with a profile link · boss → user DM ·
un-openable address recovery · no `web_app` anywhere.

## Honest limits

Live Swiggy and Telegram calls are **not** exercised by the tests (no network in
CI). The engine calls used here are the same four already running in the parent
project:

- `resolveSwiggyLink` — links → cart + address
- `findBestMaxCouponAccountForOrder` — account pick + live bill
- `generateRealSwiggyMerchantUpiQr` — real payment QR
- `checkRealSwiggyPaymentAndExtractTracking` — paid? + tracking link

Those four need one real order to confirm on your account. Everything around
them is covered by the suite.
