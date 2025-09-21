import { mkdir, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { EFFECT_FAMILIES, canCommute, parSafe } from '../packages/tf-l0-check/src/effect-lattice.mjs';

export function buildLatticeReport({ families = EFFECT_FAMILIES } = {}) {
  const uniqFamilies = Array.from(new Set(families.filter(f => typeof f === 'string' && f.length > 0)));
  const commute = {};
  const parallel = {};
  for (const famA of uniqFamilies) {
    commute[famA] = {};
    parallel[famA] = {};
    for (const famB of uniqFamilies) {
      commute[famA][famB] = canCommute(famA, famB);
      let ctx = undefined;
      if (famA === 'Storage.Write' && famB === 'Storage.Write') {
        const writes = [{ mode: 'write', uri: 'res://lattice/sample' }];
        ctx = { writesA: writes, writesB: writes };
      }
      parallel[famA][famB] = parSafe(famA, famB, ctx);
    }
  }
  return { commute, parSafe: parallel };
}

async function main() {
  const report = buildLatticeReport();
  const repoRoot = fileURLToPath(new URL('..', import.meta.url));
  const outDir = path.join(repoRoot, 'out', '0.4', 'check');
  const outPath = path.join(outDir, 'lattice-report.json');
  await mkdir(outDir, { recursive: true });
  await writeFile(outPath, JSON.stringify(report, null, 2) + '\n', 'utf8');
  return outPath;
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  main().catch((err) => {
    console.error('failed to generate lattice report', err);
    process.exitCode = 1;
  });
}
