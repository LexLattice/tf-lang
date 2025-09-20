// Judge for A0/A1: presence, determinism, sample parse+check
import { spawnSync } from 'node:child_process';
import { readFile } from 'node:fs/promises';

const score = { DoD: 0, Determinism: 0, CLI: 0, Total: 0 };

try {
  await readFile('packages/tf-l0-spec/spec/ids.json','utf8');
  await readFile('packages/tf-l0-spec/spec/version.json','utf8');
  await readFile('packages/tf-l0-spec/spec/catalog.json','utf8');
  await readFile('packages/tf-l0-spec/spec/laws.json','utf8');
  await readFile('packages/tf-l0-spec/spec/effects.json','utf8');
  score.DoD = 30;
} catch {}

try {
  const res = spawnSync('bash', ['scripts/determinism-check.sh', "npm run a0 --silent"], { stdio: 'inherit' });
  score.Determinism = res.status === 0 ? 20 : 0;
} catch {}

try {
  const parse = spawnSync('node', ['packages/tf-compose/bin/tf.mjs','parse','examples/flows/signing.tf','-o','out/0.4/ir/signing.ir.json'], { stdio: 'inherit' });
  const check = spawnSync('node', ['packages/tf-compose/bin/tf.mjs','check','examples/flows/signing.tf','-o','out/0.4/flows/signing.verdict.json'], { stdio: 'inherit' });
  score.CLI = (parse.status===0 && check.status===0) ? 10 : 0;
} catch {}

score.Total = score.DoD + score.Determinism + score.CLI;
console.log(JSON.stringify({ sprint: "A0+A1 hard-ground", score }, null, 2));
