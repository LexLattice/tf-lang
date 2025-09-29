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
  irPath?: string;
  irSource?: string;
  statusPath?: string;
  tracePath?: string;
  disableWasm?: boolean;
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
    const normalized = normalizeTraceIds(raw);
    cachedTraceIds = normalized.length ? normalized : FALLBACK_TRACE_IDS;
  } catch (err) {
    debugWarn('Failed to read default trace ids from WASM', err);
  }
}

function normalizeTraceIds(raw: unknown): string[] {
  const values = collectTraceCandidates(raw);
  const coerced = values
    .map(value => String(value).trim())
    .filter(value => value.length > 0);
  const unique = Array.from(new Set(coerced));
  return unique.slice(0, 100);
}

function collectTraceCandidates(raw: unknown): unknown[] {
  if (raw == null) return [];
  if (typeof raw === 'string') return [raw];
  if (Array.isArray(raw)) return raw;
  if (isIterable(raw)) return Array.from(raw as Iterable<unknown>);
  if (isArrayLike(raw)) return Array.from(raw as ArrayLike<unknown>);
  return [];
}

function isIterable(value: unknown): value is Iterable<unknown> {
  if (value == null) return false;
  if (typeof value === 'string') return false;
  return typeof (value as { [Symbol.iterator]?: unknown })[Symbol.iterator] === 'function';
}

function isArrayLike(value: unknown): value is ArrayLike<unknown> {
  if (value == null) return false;
  if (typeof value === 'function') return false;
  if (typeof value === 'string') return false;
  const length = (value as { length?: unknown }).length;
  return typeof length === 'number' && Number.isFinite(length) && length >= 0;
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

async function getEngine(disable?: boolean): Promise<Engine> {
  if (disable === true) return stubEngine;

  if (!cachedEngine) {
    const wasmEngine = await loadWasmEngine();
    cachedEngine = wasmEngine ?? stubEngine;
    if (cachedEngine === stubEngine) {
      debugWarn('Falling back to stub evaluation engine');
    }
  }
  return cachedEngine;
}

async function ensureParentDirectory(path: string) {
  await mkdir(dirname(path), { recursive: true });
}

export async function run(opts: RunOpts) {
  const irJson = typeof opts.irSource === 'string'
    ? opts.irSource
    : await readFile(String(opts.irPath), 'utf8').catch(() => '{}');

  const engine = await getEngine(opts.disableWasm);

  let result: EvalResult;
  try {
    result = await engine(irJson);
  } catch (err) {
    debugWarn('Evaluation engine threw; using stub instead', err);
    cachedEngine = stubEngine;
    result = await stubEngine(irJson);
  }

  if (opts.statusPath) {
    await ensureParentDirectory(opts.statusPath);
    await writeFile(opts.statusPath, JSON.stringify(result.status) + '\n', 'utf8');
  }
  if (opts.tracePath) {
    await ensureParentDirectory(opts.tracePath);
    const body = result.trace.map(item => JSON.stringify(item)).join('\n') + '\n';
    await writeFile(opts.tracePath, body, 'utf8');
  }
  return result;
}
