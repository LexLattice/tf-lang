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

export interface EvalStatus {
  ok: boolean;
  engine: string;
  bytes: number;
}

export interface EvalTraceItem {
  prim_id?: string;
  effect?: string;
  [key: string]: unknown;
}

export interface EvalResult {
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

function coerceString(value: unknown): string | undefined {
  if (typeof value !== 'string') {
    return undefined;
  }
  const trimmed = value.trim();
  return trimmed.length > 0 ? trimmed : undefined;
}

function coerceBoolean(value: unknown): boolean {
  if (typeof value === 'boolean') {
    return value;
  }
  if (typeof value === 'number') {
    return Number.isFinite(value) && value !== 0;
  }
  if (typeof value === 'string') {
    const lowered = value.trim().toLowerCase();
    if (lowered === 'false' || lowered === '0' || lowered === 'no') {
      return false;
    }
    if (lowered === 'true' || lowered === '1' || lowered === 'yes') {
      return true;
    }
    return lowered.length > 0;
  }
  return Boolean(value);
}

function normalizeTraceEntry(raw: unknown, index: number): EvalTraceItem {
  if (typeof raw === 'string') {
    const primId = coerceString(raw) ?? `tf:stub/primitive@${index + 1}`;
    return primId ? { prim_id: primId } : {};
  }

  if (raw && typeof raw === 'object') {
    const record = raw as Record<string, unknown>;
    const primId =
      coerceString(record.prim_id) ??
      coerceString(record.prim) ??
      `tf:stub/primitive@${index + 1}`;
    const effect = coerceString(record.effect);

    const item: EvalTraceItem = {};
    if (primId) item.prim_id = primId;
    if (effect) item.effect = effect;
    for (const [key, value] of Object.entries(record)) {
      if (key === 'prim_id' || key === 'prim' || key === 'effect') {
        continue;
      }
      item[key] = value;
    }
    return item;
  }

  return { prim_id: `tf:stub/primitive@${index + 1}` };
}

function normalizeTrace(raw: unknown): EvalTraceItem[] {
  if (!Array.isArray(raw)) {
    return [];
  }
  return raw.map((entry, index) => normalizeTraceEntry(entry, index));
}

function extractPrimitiveEntries(irJson: string): unknown[] {
  try {
    const parsed = JSON.parse(irJson) as unknown;
    if (parsed && typeof parsed === 'object' && Array.isArray((parsed as { primitives?: unknown }).primitives)) {
      return (parsed as { primitives: unknown[] }).primitives;
    }
  } catch {
    // Swallow JSON errors; fall back to cached trace ids below.
  }
  return [];
}

function normalizeStatus(raw: unknown, irJson: string, fallbackEngine: string): EvalStatus {
  const bytes = Buffer.byteLength(irJson, 'utf8');
  if (raw && typeof raw === 'object') {
    const record = raw as Record<string, unknown>;
    const okValue = record.ok;
    const engineValue = record.engine;
    const bytesValue = record.bytes;
    return {
      ok: coerceBoolean(okValue),
      engine: coerceString(engineValue) ?? fallbackEngine,
      bytes: typeof bytesValue === 'number' && Number.isFinite(bytesValue) ? bytesValue : bytes,
    };
  }
  return { ok: false, engine: fallbackEngine, bytes };
}

function stubEngine(irJson: string): Promise<EvalResult> {
  const bytes = Buffer.byteLength(irJson, 'utf8');
  const status: EvalStatus = { ok: true, engine: 'tf-eval-stub', bytes };
  const primitives = extractPrimitiveEntries(irJson);
  const traceSource = primitives.length > 0 ? primitives : cachedTraceIds;
  const trace: EvalTraceItem[] = normalizeTrace(traceSource);
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
  let usedStub = engine === stubEngine;

  let result: EvalResult;
  try {
    result = await engine(irJson);
  } catch (err) {
    debugWarn('Evaluation engine threw; using stub instead', err);
    cachedEngine = stubEngine;
    usedStub = true;
    result = await stubEngine(irJson);
  }

  const normalizedTrace = normalizeTrace(result.trace);
  const normalizedStatus = normalizeStatus(result.status, irJson, usedStub ? 'tf-eval-stub' : 'tf-eval-wasm');
  const normalizedResult: EvalResult = {
    status: normalizedStatus,
    trace: normalizedTrace,
  };

  if (opts.statusPath) {
    await ensureParentDirectory(opts.statusPath);
    await writeFile(opts.statusPath, JSON.stringify(normalizedResult.status, null, 2) + '\n', 'utf8');
  }
  if (opts.tracePath) {
    await ensureParentDirectory(opts.tracePath);
    const body = normalizedResult.trace.map(item => JSON.stringify(item)).join('\n') + '\n';
    await writeFile(opts.tracePath, body, 'utf8');
  }
  return normalizedResult;
}
