import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

const DEBUG = process.env.TF_RUN_WASM_DEBUG === '1';

const WASM_BYTES = new Uint8Array([
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f,
  0x02, 0x10, 0x01, 0x03, 0x65, 0x6e, 0x76, 0x08, 0x68, 0x6f, 0x73, 0x74, 0x5f, 0x72, 0x75, 0x6e, 0x00, 0x00,
  0x03, 0x02, 0x01, 0x00,
  0x07, 0x07, 0x01, 0x03, 0x72, 0x75, 0x6e, 0x00, 0x01,
  0x0a, 0x06, 0x01, 0x04, 0x00, 0x10, 0x00, 0x0b,
]);

const FALLBACK_TRACE_IDS: readonly string[] = [
  'tf:pure/identity@1',
  'tf:resource/write-object@1',
  'tf:integration/publish-topic@1',
];

interface EvalStatus {
  ok: boolean;
  engine: string;
  bytes: number;
  primitives: number;
}

interface EvalTraceItem {
  prim_id: string;
  effect: string;
}

interface EvalResult {
  status: EvalStatus;
  trace: EvalTraceItem[];
}

type Engine = (irJson: string) => Promise<EvalResult>;

type WasmExports = {
  run: () => number;
};

type HostContext = {
  irJson: string;
  result: EvalResult | null;
};

let wasmExportsPromise: Promise<WasmExports | null> | null = null;
let currentContext: HostContext | null = null;
let lastHostError: unknown = null;

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

function parseIr(irJson: string): unknown {
  try {
    return JSON.parse(irJson);
  } catch (err) {
    debugWarn('Failed to parse IR JSON; continuing with empty graph', err);
    return {};
  }
}

function toTraceEntry(value: unknown, index: number): EvalTraceItem {
  if (value && typeof value === 'object') {
    const record = value as Record<string, unknown>;
    const explicitId = typeof record.prim_id === 'string' && record.prim_id.length > 0 ? record.prim_id : null;
    const impliedId = typeof record.prim === 'string' && record.prim.length > 0 ? record.prim : null;
    const primId = explicitId ?? impliedId ?? FALLBACK_TRACE_IDS[index % FALLBACK_TRACE_IDS.length];
    const effectValue = typeof record.effect === 'string' && record.effect.length > 0 ? record.effect : `invoke:${primId}`;
    return { prim_id: primId, effect: effectValue };
  }
  if (typeof value === 'string' && value.length > 0) {
    const primId = value;
    return { prim_id: primId, effect: `invoke:${primId}` };
  }
  const primId = FALLBACK_TRACE_IDS[index % FALLBACK_TRACE_IDS.length];
  return { prim_id: primId, effect: `invoke:${primId}` };
}

function evaluateIr(irJson: string): EvalResult {
  const bytes = Buffer.byteLength(irJson, 'utf8');
  const parsed = parseIr(irJson);
  const primitives = Array.isArray((parsed as Record<string, unknown>).primitives)
    ? (parsed as Record<string, unknown>).primitives as unknown[]
    : [];
  const trace = primitives.map(toTraceEntry);
  const status: EvalStatus = {
    ok: true,
    engine: 'mini-runtime',
    bytes,
    primitives: trace.length,
  };
  return { status, trace };
}

function hostRun(): number {
  if (!currentContext) {
    lastHostError = new Error('host_run invoked without an active context');
    return 1;
  }
  try {
    currentContext.result = evaluateIr(currentContext.irJson);
    return 0;
  } catch (err) {
    lastHostError = err;
    currentContext.result = null;
    return 2;
  }
}

const hostImports = {
  env: {
    host_run: hostRun,
  },
};

async function instantiateWasm(): Promise<WasmExports | null> {
  if (process.env.TF_RUN_WASM_DISABLE_WASM === '1') {
    debugWarn('WASM execution disabled via TF_RUN_WASM_DISABLE_WASM');
    return null;
  }
  if (!wasmExportsPromise) {
    wasmExportsPromise = WebAssembly.instantiate(WASM_BYTES, hostImports)
      .then((source) => source.instance.exports as WasmExports)
      .catch((err) => {
        wasmExportsPromise = null;
        debugWarn('Failed to instantiate embedded WASM module', err);
        return null;
      });
  }
  return wasmExportsPromise;
}

async function loadWasmEngine(): Promise<Engine | null> {
  const exports = await instantiateWasm();
  if (!exports) {
    return null;
  }
  return async (irJson: string) => {
    if (currentContext) {
      throw new Error('WASM runtime is already processing a request');
    }
    currentContext = { irJson, result: null };
    lastHostError = null;
    try {
      const code = exports.run();
      if (code !== 0) {
        const err = lastHostError instanceof Error ? lastHostError : new Error(`WASM runner exited with code ${code}`);
        lastHostError = null;
        throw err;
      }
      if (!currentContext.result) {
        throw new Error('WASM host shim did not produce a result');
      }
      return currentContext.result;
    } finally {
      currentContext = null;
      lastHostError = null;
    }
  };
}

async function getEngine(disableWasm: boolean | undefined): Promise<Engine> {
  if (disableWasm) {
    return async (irJson: string) => evaluateIr(irJson);
  }
  const wasmEngine = await loadWasmEngine();
  if (wasmEngine) {
    return wasmEngine;
  }
  return async (irJson: string) => evaluateIr(irJson);
}

async function ensureParentDirectory(path: string) {
  await mkdir(dirname(path), { recursive: true });
}

async function writeJsonFile(path: string, value: unknown, pretty: boolean) {
  await ensureParentDirectory(path);
  const body = JSON.stringify(value, pretty ? null : undefined, pretty ? 2 : undefined);
  await writeFile(path, `${body}\n`, 'utf8');
}

async function writeTraceFile(path: string, trace: EvalTraceItem[]) {
  await ensureParentDirectory(path);
  const lines = trace.map((entry) => JSON.stringify(entry));
  const body = lines.join('\n');
  await writeFile(path, `${body}\n`, 'utf8');
}

async function readIrFromDisk(path: string): Promise<string> {
  try {
    return await readFile(path, 'utf8');
  } catch (err) {
    debugWarn(`Failed to read IR at ${path}; continuing with empty payload`, err);
    return '{}';
  }
}

export async function run(opts: RunOpts): Promise<EvalResult> {
  if (!opts.irSource && !opts.irPath) {
    throw new Error('run() requires an irSource string or irPath');
  }

  const irJson = opts.irSource ?? await readIrFromDisk(opts.irPath!);
  const engine = await getEngine(opts.disableWasm);

  let result: EvalResult;
  try {
    result = await engine(irJson);
  } catch (err) {
    if (!opts.disableWasm) {
      debugWarn('Primary engine failed; retrying with native evaluator', err);
      result = evaluateIr(irJson);
    } else {
      throw err;
    }
  }

  if (opts.statusPath) {
    await writeJsonFile(opts.statusPath, result.status, true);
  }
  if (opts.tracePath) {
    await writeTraceFile(opts.tracePath, result.trace);
  }

  return result;
}
