const fs = require('fs');
const path = require('path');
const readline = require('readline');
const core = require('./pilot-core/dist/index.js');

async function validateNdjson(filePath, validator) {
  const stream = fs.createReadStream(filePath, { encoding: 'utf8' });
  const rl = readline.createInterface({ input: stream, crlfDelay: Infinity });
  for await (const line of rl) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    const payload = JSON.parse(trimmed);
    validator(payload);
  }
}

(async () => {
  const framesPath = path.resolve('out/t5/replay/frames.ndjson');
  const ordersPath = path.resolve('out/t5/effects/orders.ndjson');
  const meanPath = path.resolve('out/t5/effects/orders-mean-reversion.ndjson');

  await validateNdjson(framesPath, core.validateFrame);
  await validateNdjson(ordersPath, core.validateOrder);
  await validateNdjson(meanPath, core.validateOrder);

  console.log('Artifacts validated');
})().catch((error) => {
  console.error(error);
  process.exit(1);
});
