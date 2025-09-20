import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { join } from 'node:path';
import { createHash } from 'node:crypto';

const spec = 'packages/tf-l0-spec/spec';
const outDir = 'out/0.4';

await mkdir(outDir, { recursive: true });

const ids = await readFile(join(spec, 'ids.json'));
const ver = await readFile(join(spec, 'version.json'), 'utf8');
const vh = 'sha256:' + createHash('sha256').update(ver).digest('hex');
const ih = 'sha256:' + createHash('sha256').update(ids).digest('hex');
await writeFile(join(spec, 'catalog-hash.txt'), ih + '\n', 'utf8');

const v = JSON.parse(ver);
await writeFile(join(spec, 'version.txt'), `catalog_semver=${v.catalog_semver}\ndsl_semver=${v.dsl_semver}\nir_semver=${v.ir_semver}\ntrace_semver=${v.trace_semver}\ncanonical_json=${v.canonical_json}\n`, 'utf8');

await writeFile(join(outDir, 'status.json'), JSON.stringify({
  sprint: "A0",
  done: ["spec/ids.json","spec/version.txt","spec/catalog-hash.txt"],
  partial: ["schemas/*.json"],
  todo: [],
  hashes: {"spec/ids.json": ih, "spec/version.json": vh},
  inputs: { catalog_sources: "./catalogs/*.yaml", dsl: v.dsl_semver, ir: v.ir_semver, trace: v.trace_semver },
  notes: "A0 complete"
}, null, 2) + '\n', 'utf8');
console.log("A0 finalize complete.");
