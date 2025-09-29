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
    let normalized;
    if (baseIndent && line.startsWith(baseIndent)) {
      normalized = line.slice(baseIndent.length);
    } else {
      normalized = line.trimStart();
    }
    return `${baseIndent}  ${normalized}`;
  });

  const indentedBody = indentedLines.join('\n');
  const bodySection = indentedBody ? `${indentedBody}\n` : '';
  let newText = `${baseIndent}authorize{ scope: "" } {\n${bodySection}${baseIndent}}`;
  if (trailingNewline) {
    newText += '\n';
  }

  return { newText, start: safeStart, end: safeEnd, before, after };
}
