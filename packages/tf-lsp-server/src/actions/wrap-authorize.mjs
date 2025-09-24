export function wrapWithAuthorize(src, range = {}) {
  const start = typeof range?.start === 'number' ? range.start : 0;
  const end = typeof range?.end === 'number' ? range.end : src.length;

  const safeStart = Math.max(0, Math.min(start, src.length));
  const safeEnd = Math.max(safeStart, Math.min(end, src.length));

  const before = src.slice(0, safeStart);
  const inside = src.slice(safeStart, safeEnd);
  const after = src.slice(safeEnd);

  const lines = inside.split(/\r?\n/);
  while (lines.length && !lines[lines.length - 1].trim()) {
    lines.pop();
  }

  const firstNonEmpty = lines.find(line => line.trim().length > 0);
  const baseIndent = firstNonEmpty ? (firstNonEmpty.match(/^(\s*)/)?.[1] ?? '') : '';

  const indentedBody = lines
    .map(line => {
      if (!line.trim()) return baseIndent;
      const normalized = line.startsWith(baseIndent) ? line.slice(baseIndent.length) : line.trimStart();
      return `${baseIndent}  ${normalized}`;
    })
    .join('\n');

  const trailingNewline = /\r?\n$/.test(inside);
  const bodySection = indentedBody ? `${indentedBody}\n` : '';
  let newText = `${baseIndent}Authorize{ scope: "" } {\n${bodySection}${baseIndent}}`;
  if (trailingNewline) {
    newText += '\n';
  }

  return { newText, start: safeStart, end: safeEnd, before, after };
}
