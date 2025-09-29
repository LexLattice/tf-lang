function getBaseIndent(lines) {
  for (const line of lines) {
    if (!line.trim()) continue;
    const match = line.match(/^(\s*)/);
    if (match) {
      return match[1] ?? '';
    }
    return '';
  }
  return '';
}

export function wrapWithAuthorize(src, range = {}) {
  const start = typeof range?.start === 'number' ? range.start : 0;
  const end = typeof range?.end === 'number' ? range.end : src.length;

  const safeStart = Math.max(0, Math.min(start, src.length));
  const safeEnd = Math.max(safeStart, Math.min(end, src.length));

  const before = src.slice(0, safeStart);
  const inside = src.slice(safeStart, safeEnd);
  const after = src.slice(safeEnd);

  const trailingNewline = /\r?\n$/.test(inside);
  const sourceHasFinalNewline = /\r?\n$/.test(src);
  const normalizedInside = inside.replace(/\r\n/g, '\n');
  const lines = normalizedInside.split('\n');

  if (trailingNewline && lines[lines.length - 1] === '') {
    lines.pop();
  }

  while (lines.length && !lines[lines.length - 1].trim()) {
    lines.pop();
  }

  const baseIndent = getBaseIndent(lines);

  const indentedLines = lines.map(line => {
    if (!line.trim()) {
      return '';
    }
    const indentMatch = line.match(/^(\s*)/);
    const indent = indentMatch ? indentMatch[1] ?? '' : '';
    const remainder = line.slice(indent.length);
    const relative = indent.startsWith(baseIndent) ? indent.slice(baseIndent.length) : '';
    return `${baseIndent}  ${relative}${remainder}`;
  });

  const indentedBody = indentedLines.join('\n');
  const bodySection = indentedBody ? `${indentedBody}\n` : '';
  let newText = `${baseIndent}authorize{ scope: "" } {\n${bodySection}${baseIndent}}`;
  const touchesEOF = safeEnd === src.length;
  const shouldAddFinalNewline = trailingNewline || (touchesEOF && sourceHasFinalNewline);
  if (shouldAddFinalNewline && !newText.endsWith('\n')) {
    newText += '\n';
  }

  return { newText, start: safeStart, end: safeEnd, before, after };
}
