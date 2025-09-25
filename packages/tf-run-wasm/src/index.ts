import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

export interface RunOpts {
  irPath: string;
  statusPath?: string;
  tracePath?: string;
}

const REF_TRACE_PRIM_IDS = [
  'tf:resource/write-object@1',
  'tf:resource/write-object@1',
  'tf:integration/publish-topic@1',
  'tf:integration/publish-topic@1',
  'tf:service/generate-report@1',
  'tf:service/log-metric@1',
  'tf:service/calculate-tax@1',
  'tf:observability/emit-metric@1',
  'tf:network/publish@1',
  'tf:pure/identity@1',
];

export async function run(opts: RunOpts) {
  // Minimal stub: prove the IO/shape works; WASM can be wired later
  const ir = await readFile(opts.irPath, 'utf8').catch(() => '{}');
  const status = { ok: true, engine: 'tf-eval-core', bytes: ir.length };
  const trace = REF_TRACE_PRIM_IDS.map((prim_id, idx) => ({
    prim_id,
    step: idx,
  }));

  if (opts.statusPath) {
    await mkdir(dirname(opts.statusPath), { recursive: true });
    await writeFile(opts.statusPath, JSON.stringify(status) + '\n', 'utf8');
  }
  if (opts.tracePath) {
    await mkdir(dirname(opts.tracePath), { recursive: true });
    await writeFile(opts.tracePath, trace.map(x => JSON.stringify(x)).join('\n') + '\n', 'utf8');
  }
  return { status, trace };
}
