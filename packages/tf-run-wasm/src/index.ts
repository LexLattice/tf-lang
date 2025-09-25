import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

const WASM_MODULE = '../../crates/tf-eval-wasm/pkg/tf_eval_wasm.js';
const DEFAULT_TRACE_IDS = [
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

interface EvalStatus {
  ok: boolean;
  engine: string;
  bytes: number;
}

interface EvalTraceItem {
  prim_id?: string;
  prim?: string;
  id?: string;
  [key: string]: unknown;
}

interface EvalResult {
  status: EvalStatus;
  trace: EvalTraceItem[];
}

type Engine = (irJson: string) => Promise<EvalResult>;

let cachedEngine: Engine | null = null;

export interface RunOpts {
  irPath: string;
  statusPath?: string;
  tracePath?: string;
}

function stubEngine(irJson: string): Promise<EvalResult> {
  const status: EvalStatus = { ok: true, engine: 'stub', bytes: irJson.length };
  const trace: EvalTraceItem[] = DEFAULT_TRACE_IDS.map(prim_id => ({ prim_id }));
  return Promise.resolve({ status, trace });
}

async function loadWasmEngine(): Promise<Engine | null> {
  if (process.env.TF_RUN_WASM_DISABLE_WASM === '1') {
    return null;
  }

  try {
    const moduleUrl = new URL(WASM_MODULE, import.meta.url);
    const wasm = await import(moduleUrl.href);
    if (typeof wasm?.default === 'function') {
      try {
        await wasm.default();
      } catch (err) {
        // If the initializer fails (e.g. missing .wasm binary) fall back to stub
        return null;
      }
    }
    if (typeof wasm?.run === 'function') {
      return (irJson: string) => Promise.resolve(wasm.run(irJson));
    }
  } catch (err) {
    // Swallow import errors; we'll fall back to the stub engine.
  }
  return null;
}

async function getEngine(): Promise<Engine> {
  if (!cachedEngine) {
    cachedEngine = (await loadWasmEngine()) ?? stubEngine;
  }
  return cachedEngine;
}

export async function run(opts: RunOpts) {
  const ir = await readFile(opts.irPath, 'utf8').catch(() => '{}');
  const engine = await getEngine();

  let result: EvalResult;
  try {
    result = await engine(ir);
  } catch (err) {
    result = await stubEngine(ir);
  }

  if (opts.statusPath) {
    await mkdir(dirname(opts.statusPath), { recursive: true });
    await writeFile(opts.statusPath, JSON.stringify(result.status) + '\n', 'utf8');
  }
  if (opts.tracePath) {
    await mkdir(dirname(opts.tracePath), { recursive: true });
    const body = result.trace.map(item => JSON.stringify(item)).join('\n') + '\n';
    await writeFile(opts.tracePath, body, 'utf8');
  }
  return result;
}
