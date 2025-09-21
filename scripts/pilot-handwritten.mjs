#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { mkdir, writeFile, rm } from 'node:fs/promises';
import { join, dirname, isAbsolute } from 'node:path';
import { fileURLToPath } from 'node:url';
import inmem from '../packages/tf-l0-codegen-ts/src/runtime/inmem.mjs';
import { canonicalStringify } from './hash-jsonl.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');
const FIXED_TS = process.env.TF_FIXED_TS || '1750000000000';
const baseEnv = { ...process.env, TF_FIXED_TS: String(FIXED_TS) };

function resolveOutDir() {
  const override = process.env.PILOT_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  return join(rootDir, 'out', '0.4', 'pilot-l0');
}

const outDir = resolveOutDir();
const manualDir = join(outDir, 'manual');
const manifestPath = join(outDir, 'pilot_min.manifest.json');
const statusPath = join(manualDir, 'status.json');
const tracePath = join(manualDir, 'trace.jsonl');
const summaryPath = join(manualDir, 'summary.json');
const traceSummary = join(rootDir, 'packages', 'tf-l0-tools', 'trace-summary.mjs');

async function removeIfExists(path) {
  await rm(path, { recursive: true, force: true });
}

async function main() {
  await mkdir(manualDir, { recursive: true });
  await removeIfExists(statusPath);
  await removeIfExists(tracePath);
  await removeIfExists(summaryPath);

  const prevStatus = process.env.TF_STATUS_PATH;
  const prevTrace = process.env.TF_TRACE_PATH;
  const prevFixedTs = process.env.TF_FIXED_TS;

  process.env.TF_STATUS_PATH = statusPath;
  process.env.TF_TRACE_PATH = tracePath;
  process.env.TF_FIXED_TS = String(FIXED_TS);

  try {
    inmem.reset?.();

    const operations = [
      { prim: 'tf:observability/emit-metric@1', args: { name: 'pilot.replay.start' } },
      {
        prim: 'tf:network/publish@1',
        args: { key: 'o-1', payload: '{"sym":"ABC","side":"buy","qty":1}', topic: 'orders' },
      },
      { prim: 'tf:observability/emit-metric@1', args: { name: 'pilot.exec.sent' } },
      { prim: 'tf:resource/write-object@1', args: { uri: 'res://ledger/pilot', key: 'o-1', value: 'filled' } },
      { prim: 'tf:observability/emit-metric@1', args: { name: 'pilot.ledger.write' } },
    ];

    const effects = new Set();
    const traceLines = [];

    const baseTs = BigInt(process.env.TF_FIXED_TS || FIXED_TS);
    let offset = 0n;

    for (const { prim, args } of operations) {
      const adapter = typeof inmem.getAdapter === 'function' ? inmem.getAdapter(prim) : inmem[prim];
      if (typeof adapter !== 'function') {
        throw new Error(`pilot-handwritten: missing adapter for ${prim}`);
      }
      const canonicalPrim = typeof inmem.canonicalPrim === 'function' ? inmem.canonicalPrim(prim) : prim;
      const effect = typeof inmem.effectFor === 'function' ? inmem.effectFor(prim) : '';
      if (typeof effect === 'string' && effect) {
        effects.add(effect);
      }
      const ts = Number(baseTs + offset);
      const record = {
        ts,
        prim_id: canonicalPrim,
        args,
        region: '',
        effect: typeof effect === 'string' ? effect : '',
      };
      traceLines.push(JSON.stringify(record));
      await adapter(args, inmem.state ?? {});
      offset += 1n;
    }

    await writeFile(tracePath, traceLines.join('\n') + '\n');

    const summaryProc = spawnSync('node', [traceSummary], {
      input: traceLines.join('\n') + '\n',
      encoding: 'utf8',
      env: baseEnv,
    });
    if (summaryProc.status !== 0) {
      throw new Error('pilot-handwritten: trace-summary failed');
    }
    const summaryJson = JSON.parse(summaryProc.stdout);
    await writeFile(summaryPath, canonicalStringify(summaryJson) + '\n');

    const status = {
      ok: true,
      ops: operations.length,
      effects: Array.from(effects).sort(),
      manifest_path: manifestPath,
    };
    await writeFile(statusPath, JSON.stringify(status, null, 2) + '\n');
  } finally {
    if (prevStatus === undefined) delete process.env.TF_STATUS_PATH;
    else process.env.TF_STATUS_PATH = prevStatus;
    if (prevTrace === undefined) delete process.env.TF_TRACE_PATH;
    else process.env.TF_TRACE_PATH = prevTrace;
    if (prevFixedTs === undefined) delete process.env.TF_FIXED_TS;
    else process.env.TF_FIXED_TS = prevFixedTs;
  }

  console.log('pilot-handwritten: completed manual artifacts in', manualDir);
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
