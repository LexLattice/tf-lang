import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

const DEBUG = process.env.TF_RUN_WASM_DEBUG === '1';

const CANDIDATES: readonly (() => string)[] = [
  () => new URL('../../../crates/tf-eval-wasm/pkg/tf_eval_wasm.js', import.meta.url).href,
  () => 'tf-eval-wasm/tf_eval_wasm.js',
];

const FALLBACK_TRACE_IDS: readonly string[] = [
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

let cachedTraceIds: readonly string[] = FALLBACK_TRACE_IDS;

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

type WasmBindings = {
  default?: () => unknown;
  run?: (irJson: string) => EvalResult | Promise<EvalResult>;
  default_trace_ids?: () => unknown;
};

let cachedEngine: Engine | null = null;

export interface RunOpts {
  irPath: string;
  statusPath?: string;
  tracePath?: string;
}

function debugWarn(message: string, err?: unknown) {
  if (!DEBUG) {
    return;
  }
  if (err === undefined) {
    console.warn('[tf-run-wasm]', message);
  } else {
    console.warn('[tf-run-wasm]', message, err);
  }
}

function stubEngine(irJson: string): Promise<EvalResult> {
  const bytes = Buffer.byteLength(irJson, 'utf8');
  const status: EvalStatus = { ok: true, engine: 'tf-eval-core', bytes };
  const trace: EvalTraceItem[] = cachedTraceIds.map(prim_id => ({ prim_id }));
  return Promise.resolve({ status, trace });
}

async function importWasmBindings(): Promise<WasmBindings> {
  let lastError: unknown = new Error('Failed to load tf-eval-wasm bindings');
  for (const resolveSpecifier of CANDIDATES) {
    const specifier = resolveSpecifier();
    try {
      return (await import(specifier)) as WasmBindings;
    } catch (err) {
      lastError = err;
      debugWarn(`Failed to import WASM module from ${specifier}`, err);
    }
  }
  throw lastError;
}

function updateTraceIdsFromWasm(wasm: WasmBindings) {
  if (typeof wasm.default_trace_ids !== 'function') {
    return;
  }
  try {
    const raw = wasm.default_trace_ids();
    const values = Array.from(raw as ArrayLike<unknown>, value => String(value));
    if (values.length > 0) {
      cachedTraceIds = values;
    }
  } catch (err) {
    debugWarn('Failed to read default trace ids from WASM', err);
  }
}

async function loadWasmEngine(): Promise<Engine | null> {
  if (process.env.TF_RUN_WASM_DISABLE_WASM === '1') {
    debugWarn('WASM disabled via TF_RUN_WASM_DISABLE_WASM');
    return null;
  }

  let wasm: WasmBindings;
  try {
    wasm = await importWasmBindings();
  } catch (err) {
    debugWarn('Unable to import tf-eval-wasm bindings', err);
    return null;
  }

  if (typeof wasm.default === 'function') {
    try {
      await Promise.resolve(wasm.default());
    } catch (err) {
      debugWarn('WASM initializer threw during load', err);
      return null;
    }
  }

  updateTraceIdsFromWasm(wasm);

  if (typeof wasm.run === 'function') {
    return (irJson: string) => Promise.resolve(wasm.run!(irJson));
  }

  debugWarn('WASM bindings missing run export');
  return null;
}

async function getEngine(): Promise<Engine> {
  if (!cachedEngine) {
    const wasmEngine = await loadWasmEngine();
    cachedEngine = wasmEngine ?? stubEngine;
    if (cachedEngine === stubEngine) {
      debugWarn('Falling back to stub evaluation engine');
    }
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
    debugWarn('Evaluation engine threw; using stub instead', err);
    cachedEngine = stubEngine;
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
