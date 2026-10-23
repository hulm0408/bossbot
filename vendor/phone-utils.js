// Strict Indian mobile-number helpers shared by intake and Swiggy account flows.
// Login accepts a bare 10-digit mobile or its 12-digit 91-prefixed form only.
export function normalizeIndianMobileNumber(value) {
  if (value === null || value === undefined) return null;
  const text = String(value).trim();
  if (!text || !/^\+?[\d\s-]+$/.test(text)) return null;

  const digits = text.replace(/\D/g, '');
  if (/^[6-9]\d{9}$/.test(digits)) return digits;
  if (/^91[6-9]\d{9}$/.test(digits)) return digits.slice(2);
  return null;
}

// Returns a normalized number only when the entire message is just the number.
// Never extract digits from an address, URL, JSON, or sentence.
export function extractStandaloneMobileNumber(rawText) {
  if (typeof rawText !== 'string') return null;
  const trimmed = rawText.trim();
  if (trimmed.length < 10 || trimmed.length > 18) return null;
  if (/https?:\/\/|swig\.gy|swiggy|goo\.gl|maps|cart|flat|house|floor|road|nagar|colony|sector|[{[\]@\\/a-z]/i.test(trimmed)) {
    return null;
  }

  const match = trimmed.match(/^(?:\+?91[\s-]?)?([6-9]\d{4}[\s-]?\d{5})$/);
  if (!match) return null;
  return normalizeIndianMobileNumber(trimmed);
}
