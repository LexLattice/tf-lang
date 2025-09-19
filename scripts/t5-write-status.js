#!/usr/bin/env node
import('../packages/pilot-core/dist/index.js').then(({ writeStatusFile }) => {
  const seed = 42;
  const slice = '0:50:1';
  writeStatusFile({
    seed,
    slice,
    files: {
      'frames.ndjson': { path: 'out/t5/replay/frames.ndjson' },
      'orders.ndjson': { path: 'out/t5/effects/orders.ndjson' },
      'evaluations.ndjson': { path: 'out/t5/risk/evaluations.ndjson' },
    },
    outPath: 'out/t5/status.json',
  });
}).catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
