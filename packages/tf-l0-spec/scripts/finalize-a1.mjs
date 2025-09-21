import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { join } from 'node:path';
import { createHash } from 'node:crypto';

import { canonicalize } from '../../tf-l0-ir/src/hash.mjs';
import { parseDSL } from '../../tf-compose/src/parser.mjs';
import { normalize } from '../../tf-l0-ir/src/normalize.mjs';
import { checkAuthorize } from '../../tf-l0-check/src/authorize.mjs';

const spec = 'packages/tf-l0-spec/spec';
const outDir = 'out/0.4';
await mkdir(outDir, { recursive: true });

const catalogPath = join(spec, 'catalog.json');
const cat = await readFile(catalogPath);
const ch = 'sha256:' + createHash('sha256').update(cat).digest('hex');
await writeFile(join(spec, 'catalog-hash.txt'), ch + '\n', 'utf8');

const status = {
  sprint: "A1",
  done: ["spec/catalog.json","spec/effects.json","spec/laws.json","spec/catalog-hash.txt"],
  partial: [],
  todo: [],
  hashes: {"spec/catalog.json": ch},
  inputs: { ids: "spec/ids.json" },
  notes: "A1 groundwork complete (skeletons)"
};
await writeFile(join(outDir, 'status.json'), JSON.stringify(status, null, 2) + '\n', 'utf8');

await writeAuthorizeChecks();
console.log("A1 finalize complete.");

async function writeAuthorizeChecks() {
  const policyDir = join(process.cwd(), outDir, 'check', 'policy');
  await mkdir(policyDir, { recursive: true });

  const flows = [
    { flow: 'examples/flows/auth_ok.tf', out: 'auth_ok.json' },
    { flow: 'examples/flows/auth_wrong_scope.tf', out: 'auth_wrong_scope.json' },
    { flow: 'examples/flows/auth_missing.tf', out: 'auth_missing.json' }
  ];

  const rulesPath = join(process.cwd(), 'packages', 'tf-l0-check', 'rules', 'authorize-scopes.json');
  const rules = JSON.parse(await readFile(rulesPath, 'utf8'));
  const catalog = JSON.parse(cat.toString('utf8'));

  for (const entry of flows) {
    const flowPath = join(process.cwd(), entry.flow);
    const flowSource = await readFile(flowPath, 'utf8');
    const ir = normalize(parseDSL(flowSource));
    const verdict = checkAuthorize(ir, catalog, rules, { warnUnused: false, strictWarnsFail: false });
    const payload = {
      ok: Boolean(verdict?.ok),
      reasons: [...(verdict?.reasons || [])],
      warnings: [...(verdict?.warnings || [])]
    };

    const outputPath = join(policyDir, entry.out);
    await writeFile(outputPath, canonicalize(payload) + '\n', 'utf8');
  }
}
