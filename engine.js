// ============================================================================
// engine.js — thin adapter over the proven Swiggy engine (vendor/).
// Everything Swiggy-specific lives there; this file only translates between the
// bot's short order objects and the engine's call shapes. Nothing else in the
// project is allowed to touch vendor/ directly.
// ============================================================================

import {
  resolveSwiggyLink,
  findBestMaxCouponAccountForOrder,
  generateRealSwiggyMerchantUpiQr,
  checkRealSwiggyPaymentAndExtractTracking,
  geocodeAddressDetails
} from './vendor/swiggy-cart.js';
import {
  getDb,
  importSessionJson,
  exportSessionJson,
  permanentLogoutAccount
} from './vendor/store.js';

export const URL_RE = /https?:\/\/[^\s<>"')\]]+/gi;

export function extractUrls(text) {
  return [...String(text || '').matchAll(URL_RE)].map((m) => m[0].replace(/[.,;]+$/, ''));
}

// Cart / group-cart links only. A tracking link is never a cart.
export function isCartLink(url) {
  const s = String(url || '').toLowerCase();
  if (!/swig\.gy|swiggy\.com|onelink\.me/.test(s)) return false;
  if (/r\.swiggy\.com|\/ofo\/track|\/track\/|ofo\/address|onelink\.me\/[a-z0-9]+\/[a-z0-9_-]+$/.test(s)) return false;
  return /\/gc\/|group-cart|group_cart|groupcartid|\/cart|\/menu|restaurant_id/.test(s) && !/\/restaurants\//.test(s)
    ? true
    : /\/gc\/|group-cart|group_cart|groupcartid/.test(s);
}

// Swiggy shared-address links and map pins.
export function isAddressLink(url) {
  const s = String(url || '').toLowerCase();
  if (/\/gc\/|group-cart|group_cart/.test(s)) return false;
  return /swiggy\.onelink\.me\//.test(s) ||
    /onelink\.me\/[a-z0-9]+\/[a-z0-9_-]+/.test(s) ||
    /swiggy\.com\/ofo\/address\//.test(s) ||
    /maps\.app\.goo\.gl|google\.[a-z.]+\/maps|goo\.gl\/maps/.test(s);
}

// "Flat 4, Gomti Nagar, Lucknow 226010" — typed address, no link.
export function looksLikeAddress(text) {
  const s = String(text || '').trim();
  if (s.length < 12 || s.length > 400) return false;
  if (extractUrls(s).length) return false;
  if (/^\/|^\d{1,2}$/.test(s)) return false;
  return /[a-z]{3,}/i.test(s) && /\d/.test(s) && (s.match(/,/g) || []).length >= 1;
}

export function createEngine() {
  return {
    isCartLink,
    isAddressLink,
    extractUrls,
    looksLikeAddress,

    /** Resolve both links into coordinates-free order seed data. */
    async resolve({ cart, address }) {
      const out = { cartDetails: null, addressDetails: null, restaurantName: '', restaurantId: null, groupCartId: null, hostName: null };
      const [cartMeta, addrMeta] = await Promise.all([
        cart ? resolveSwiggyLink(cart).catch(() => null) : null,
        address ? resolveSwiggyLink(address).catch(() => null) : null
      ]);
      if (cartMeta?.cartDetails) out.cartDetails = cartMeta.cartDetails;
      if (cartMeta?.restaurantName) out.restaurantName = cartMeta.restaurantName;
      if (cartMeta?.restaurantId) out.restaurantId = cartMeta.restaurantId;
      if (cartMeta?.groupCartId) out.groupCartId = cartMeta.groupCartId;
      if (cartMeta?.hostName) out.hostName = cartMeta.hostName;
      const ad = addrMeta?.addressDetails || null;
      out.addressDetails = ad && !ad.unresolvableShortLink ? ad : null;
      // A typed / pinned address has no link to resolve — geocode it instead.
      if (!out.addressDetails && address && !/^https?:\/\//i.test(String(address))) {
        const geo = await geocodeAddressDetails({ address: String(address) }).catch(() => null);
        if (geo?.address) out.addressDetails = geo;
      }
      out.addressUnresolved = Boolean(ad?.unresolvableShortLink);
      out.addressReason = ad?.unresolvedReason || '';
      return out;
    },

    /** Pick the best account + live bill. Returns the engine's own result. */
    async bill(order) {
      const probe = {
        id: order.id,
        cart: order.cart,
        address: order.address,
        addressDetails: order.addressDetails,
        cartDetails: order.cartDetails,
        restaurantId: order.restaurantId,
        groupCartId: order.groupCartId,
        hostName: order.hostName,
        items: order.items || [],
        restaurantName: order.restaurantName || '',
        status: 'PENDING',
        paymentStatus: 'UNPAID'
      };
      const res = await findBestMaxCouponAccountForOrder(probe, { captureScreenshot: false });
      if (!res?.success) return { ok: false, error: res?.error || 'Could not price this cart.', code: res?.code };
      return {
        ok: true,
        accountKey: res.winningKey || probe.selectedAccount || '',
        items: probe.items || [],
        payable: Number(probe.finalPayable || probe.totalPayable || res.probeOrder?.finalPayable || 0),
        savings: Number(probe.totalSavings || 0),
        restaurant: probe.restaurantName || res.probeOrder?.restaurantName || order.restaurantName || '',
        paymentUrl: res.paymentUrl || '',
        order: probe
      };
    },

    /** Create the real Swiggy payment QR for a confirmed order. */
    async qr(accountKey, order) {
      const account = getDb()?.config?.accounts?.[accountKey];
      if (!account) throw new Error('Account is no longer in the vault.');
      // Swiggy needs a contact on the delivery address. The share link carries it;
      // a typed address may not, so fall back to the account's own number instead
      // of asking the customer for one more field.
      if (order?.addressDetails && !order.addressDetails.mobile) {
        order.addressDetails.mobile = String(account.phone || account.mobile || '').replace(/\D/g, '').slice(-10);
      }
      const res = await generateRealSwiggyMerchantUpiQr({ account, order });
      return {
        upiIntentUrl: res.upiIntentUrl,
        amount: Number(res.amount || order.payable || 0),
        swiggyOrderId: res.swiggyOrderId || res.orderId || '',
        paymentTxnId: res.paymentTxnId || '',
        restaurant: res.restaurantName || order.restaurantName || ''
      };
    },

    /** Has this QR been paid? Returns the engine's payment/tracking payload. */
    async paid(accountKey, order) {
      const account = getDb()?.config?.accounts?.[accountKey];
      if (!account) return { paid: false, error: 'Account missing from vault.' };
      return checkRealSwiggyPaymentAndExtractTracking({ account, order });
    },

    /** Import a Swiggy session JSON (pasted text or uploaded file). */
    addSession(rawText) {
      return importSessionJson(rawText, null);
    },

    exportSession(key) {
      return exportSessionJson(key);
    },

    logout(key) {
      return permanentLogoutAccount(key, { purgeVault: true });
    }
  };
}
