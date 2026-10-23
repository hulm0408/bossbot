// ============================================================================
// Shared-link extraction
// ----------------------------------------------------------------------------
// Swiggy (and Telegram) share "Save my address / Order from ... on Swiggy"
// messages look like:
//
//   Hey! Save my address on Swiggy using the link:[https://swiggy.onelink.me/JgkQ/kubail4a](https://swiggy.onelink.me/JgkQ/kubail4a).
//   Address: ...
//   It is a one time use link and will be valid for 24 hours.
//
// Only the URL carries meaning. A naive `https?:\/\/[^\s]+` match captures
// `...kubail4a](https://...kubail4a` as ONE url, which then breaks resolution,
// classification and leaks the marketing/expiry text into the order card.
// These helpers always return the bare, de-duplicated URLs.
// ============================================================================

const MARKDOWN_LINK_RE = /\[([^\]]*)\]\(\s*(https?:\/\/[^)\s]+)\s*\)/gi;
const PLAIN_URL_RE = /https?:\/\/[^\s<>"'\]\)]+/gi;
const BARE_HOST_RE = /(?:^|[\s(\[])((?:www\.|maps\.app\.goo\.gl\/|goo\.gl\/maps|swig\.gy\/|t\.me\/)[^\s<>"'\]\)]+)/gi;

// Turns any pasted form into one clean URL (or '' when it is not a URL).
export function normalizeSharedUrl(raw) {
  if (!raw) return '';
  let value = String(raw).trim();
  if (!value) return '';

  // `[label](url)` -> `url`
  const markdown = value.match(/\[[^\]]*\]\(\s*(https?:\/\/[^)\s]+)\s*\)/i);
  if (markdown) value = markdown[1];

  // `url](url` / `url)(url` duplication produced by a broken markdown paste.
  const duplicated = value.match(/^(https?:\/\/\S*?)\]\(\s*(https?:\/\/\S*)$/);
  if (duplicated) value = duplicated[1];

  value = value
    .replace(/^[<(\[]+/, '')
    .split(/\]\(/)[0]
    .split(/\)\s*\(/)[0]
    .replace(/[>)\]}]+$/, '')
    .replace(/[.,;:!?'"]+$/, '')
    .trim();

  if (!/^https?:\/\//i.test(value)) {
    if (/^(?:www\.|maps\.app\.goo\.gl\/|goo\.gl\/maps|swig\.gy\/|t\.me\/)/i.test(value)) {
      return `https://${value.replace(/^\/+/, '')}`;
    }
    return '';
  }

  // A URL must have a host; drop truncated fragments like `https://`.
  try {
    const parsed = new URL(value);
    if (!parsed.hostname || !parsed.hostname.includes('.')) return '';
  } catch {
    return '';
  }
  return value;
}

// Every distinct URL in a message, in the order they appear — markdown links,
// plain links and bare hosts alike. Surrounding text is never included.
export function extractSharedUrls(text) {
  if (!text) return [];
  const raw = String(text);
  const seen = new Set();
  const urls = [];
  const push = (candidate) => {
    const url = normalizeSharedUrl(candidate);
    if (!url) return;
    const key = url.replace(/\/+$/, '');
    if (seen.has(key)) return;
    seen.add(key);
    urls.push(url);
  };

  for (const match of raw.matchAll(MARKDOWN_LINK_RE)) push(match[2]);
  for (const match of raw.matchAll(PLAIN_URL_RE)) push(match[0]);
  for (const match of raw.matchAll(BARE_HOST_RE)) push(match[1]);
  return urls;
}

// Removes every link (and the markdown wrappers around it) so only human text
// remains — used when deciding "is this message just a link?".
export function stripSharedLinks(text) {
  if (!text) return '';
  const cleaned = String(text)
    .replace(MARKDOWN_LINK_RE, ' ')
    .replace(PLAIN_URL_RE, ' ')
    .replace(/\[\s*\]|\(\s*\)/g, ' ')
    .replace(/[ \t]{2,}/g, ' ')
    .replace(/\n{3,}/g, '\n\n')
    .trim();

  // Nested pastes like `[[url](url)](url](url))` leave pure bracket tokens
  // behind (`](` , `[` , `))`). Drop any token made only of brackets/punctuation.
  return cleaned
    .split(/\n/)
    .map((line) => line
      .split(' ')
      .filter((token) => !/^[\[\]()\{\}.,;:'"\-]+$/.test(token))
      .join(' ')
      .trim())
    .filter((line, index, lines) => line.length > 0 || (index > 0 && lines[index - 1].length > 0))
    .join('\n')
    .trim();
}

// Replaces every `[label](url)` with the bare `url` so the same link no longer
// appears twice in the text (used when splitting multiple orders in one paste).
export function collapseSharedLinks(text) {
  if (!text) return '';
  return String(text).replace(MARKDOWN_LINK_RE, (_m, _label, url) => url);
}

// True when the message is essentially only a share link (plus telegram fluff).
export function isLinkOnlyShareText(text) {
  const remaining = stripSharedLinks(text)
    .replace(/hey!?\s*save my address on swiggy using the link\s*:?/gi, '')
    .replace(/it is a one\s*time use link.*$/gis, '')
    .replace(/[^A-Za-z0-9]/g, '');
  return remaining.length === 0;
}
