import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

export interface RunOpts {
  irPath: string;
  statusPath?: string;
  tracePath?: string;
}

export async function run(opts: RunOpts) {
  // Minimal stub: prove the IO/shape works; WASM can be wired later
  const ir = await readFile(opts.irPath, 'utf8').catch(() => '{}');
  const status = { ok: true, engine: 'stub', bytes: ir.length };
  const trace = [{ prim_id: 'stub:init' }, { prim_id: 'stub:done' }];

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
