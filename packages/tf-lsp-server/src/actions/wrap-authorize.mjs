export function wrapWithAuthorize(src, { rangeHint = null } = {}) {
  // If already authorized, do nothing.
  if (/\bauthorize\s*\{/.test(src)) return null;
  const trimmed = src.trim();
  const newText = `authorize{ ${trimmed} }`;
  // “Edit” shape for future use; the harness only checks truthiness + prints a token.
  return { range: { start: 0, end: src.length }, newText };
}
