import { canonicalJsonBytes } from "../canon/json.js";

export interface Step {
  op: string;
  params: Record<string, unknown>;
}

export interface TfSpec {
  version: string;
  name: string;
  steps: Step[];
}

type Validator = (p: Record<string, unknown>) => void;
const STEP_VALIDATORS: Record<string, Validator> = {
  copy: p => {
    if (typeof p.src !== "string") throw new Error("E_SPEC_PARAM_SRC");
    if (typeof p.dest !== "string") throw new Error("E_SPEC_PARAM_DEST");
  },
  create_network: p => {
    if (typeof p.cidr !== "string") throw new Error("E_SPEC_PARAM_CIDR");
  },
  create_vm: p => {
    if (typeof p.image !== "string") throw new Error("E_SPEC_PARAM_IMAGE");
    if (typeof p.cpus !== "number") throw new Error("E_SPEC_PARAM_CPUS");
  },
};

function load(input: string | Uint8Array | object): unknown {
  if (typeof input === "string") return JSON.parse(input);
  if (input instanceof Uint8Array) return JSON.parse(new TextDecoder().decode(input));
  return input;
}

function assertObject(val: unknown, code: string): asserts val is Record<string, unknown> {
  if (typeof val !== "object" || val === null) throw new Error(code);
}

function parseStep(raw: unknown): Step {
  assertObject(raw, "E_SPEC_STEP");
  const { op, params } = raw as Record<string, unknown>;
  if (typeof op !== "string") throw new Error("E_SPEC_OP");
  assertObject(params, "E_SPEC_PARAMS");
  const validator = STEP_VALIDATORS[op];
  if (!validator) throw new Error("E_SPEC_OP_UNKNOWN");
  validator(params);
  return { op, params };
}

export function parseSpec(input: string | Uint8Array | object): TfSpec {
  const root = load(input);
  assertObject(root, "E_SPEC_TYPE");
  if ((root as Record<string, unknown>).version !== "0.1") throw new Error("E_SPEC_VERSION");
  const name = (root as Record<string, unknown>).name;
  if (typeof name !== "string") throw new Error("E_SPEC_NAME");
  const stepsRaw = (root as Record<string, unknown>).steps;
  if (!Array.isArray(stepsRaw)) throw new Error("E_SPEC_STEPS");
  const steps = stepsRaw.map(parseStep);
  return { version: "0.1", name, steps };
}

export function serializeSpec(spec: TfSpec): Uint8Array {
  return canonicalJsonBytes(spec);
}
