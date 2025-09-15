import { canonicalJsonBytes } from "../canon/json.js";

export interface Step {
  op: "copy" | "create_vm" | "create_network";
  params: Record<string, unknown>;
}

export interface TfSpec {
  version: string;
  name: string;
  steps: Step[];
}

function isRecord(v: unknown): v is Record<string, unknown> {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}

function validateParams(op: Step["op"], params: Record<string, unknown>): void {
  const keys = Object.keys(params);
  const expect = (name: string, type: string) => {
    if (typeof params[name] !== type) throw new Error(`E_${op.toUpperCase()}_${name.toUpperCase()}`);
  };
  const checkExtras = (allowed: string[]) => {
    for (const k of keys) if (!allowed.includes(k)) throw new Error(`E_${op.toUpperCase()}_PARAM`);
  };
  switch (op) {
    case "copy": {
      expect("src", "string");
      expect("dest", "string");
      checkExtras(["src", "dest"]);
      break;
    }
    case "create_vm": {
      expect("image", "string");
      if (typeof params.cpus !== "number" || !Number.isInteger(params.cpus) || params.cpus <= 0)
        throw new Error("E_CREATE_VM_CPUS");
      checkExtras(["image", "cpus"]);
      break;
    }
    case "create_network": {
      expect("cidr", "string");
      checkExtras(["cidr"]);
      break;
    }
  }
}

export function parseSpec(input: string | Uint8Array | object): TfSpec {
  const obj =
    typeof input === "string"
      ? JSON.parse(input)
      : input instanceof Uint8Array
      ? JSON.parse(new TextDecoder().decode(input))
      : input;
  if (!isRecord(obj)) throw new Error("E_SPEC_TYPE");
  const { version, name, steps } = obj;
  if (version !== "0.1") throw new Error("E_SPEC_VERSION");
  if (typeof name !== "string") throw new Error("E_SPEC_NAME");
  if (!Array.isArray(steps)) throw new Error("E_SPEC_STEPS");

  const parsed = steps.map(s => {
    if (!isRecord(s)) throw new Error("E_SPEC_STEP");
    const { op, params } = s;
    if (op !== "copy" && op !== "create_vm" && op !== "create_network")
      throw new Error("E_SPEC_OP");
    if (!isRecord(params)) throw new Error("E_SPEC_PARAMS");
    validateParams(op, params);
    return { op, params } as Step;
  });

  return { version, name, steps: parsed };
}

export function serializeSpec(spec: TfSpec): Uint8Array {
  return canonicalJsonBytes(spec);
}
