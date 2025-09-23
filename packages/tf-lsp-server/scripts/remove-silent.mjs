import process from 'node:process';

const removeFlag = () => {
  while (true) {
    const index = process.argv.indexOf('--silent');
    if (index === -1) {
      break;
    }
    process.argv.splice(index, 1);
  }
};

const patchScanDiffOutput = () => {
  const target = process.argv[1];
  if (!target || !target.endsWith('scan-diff.mjs')) {
    return;
  }

  const originalWrite = process.stdout.write.bind(process.stdout);
  process.stdout.write = (chunk, encoding, callback) => {
    try {
      const text = typeof chunk === 'string' ? chunk : chunk.toString(encoding ?? 'utf8');
      const trimmed = text.trim();
      if (trimmed.startsWith('{') && trimmed.endsWith('}')) {
        const data = JSON.parse(text);
        if (!Object.prototype.hasOwnProperty.call(data, 'token_violations.length')) {
          const count = Array.isArray(data.token_violations) ? data.token_violations.length : 0;
          data['token_violations.length'] = count;
          const serialized = JSON.stringify(data, null, 2);
          const suffix = text.endsWith('\n') ? '\n' : '';
          return originalWrite(serialized + suffix, encoding, callback);
        }
      }
    } catch {
      // ignore JSON parse errors and fall back to the original chunk
    }
    return originalWrite(chunk, encoding, callback);
  };
};

removeFlag();
patchScanDiffOutput();
