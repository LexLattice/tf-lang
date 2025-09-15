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

const decoder = new TextDecoder();

export function parseSpec(input: string | Uint8Array | object): TfSpec {
  let obj: unknown;
  if (typeof input === "string") {
    obj = JSON.parse(input);
  } else if (input instanceof Uint8Array) {
    obj = JSON.parse(decoder.decode(input));
  } else {
    obj = input;
  }
  if (typeof obj !== "object" || obj === null) throw new Error("E_SPEC_TYPE");
  const root = obj as Record<string, unknown>;
  const allowedRoot = ["version", "name", "steps"];
  for (const k of Object.keys(root)) {
    if (!allowedRoot.includes(k)) throw new Error(`E_SPEC_FIELD: ${k}`);
  }
  if (root.version !== "0.1") throw new Error("E_SPEC_VERSION");
  if (typeof root.name !== "string") throw new Error("E_SPEC_NAME");
  if (!Array.isArray(root.steps)) throw new Error("E_SPEC_STEPS");
  const steps: Step[] = [];
  for (const [i, s] of (root.steps as unknown[]).entries()) {
    if (typeof s !== "object" || s === null) throw new Error(`E_SPEC_STEP: steps[${i}]`);
    const step = s as Record<string, unknown>;
    for (const k of Object.keys(step)) {
      if (!["op", "params"].includes(k)) {
        throw new Error(`E_SPEC_STEP_FIELD: steps[${i}].${k}`);
      }
    }
    if (typeof step.op !== "string") throw new Error(`E_SPEC_OP: steps[${i}]`);
    if (typeof step.params !== "object" || step.params === null) {
      throw new Error(`E_SPEC_PARAMS: steps[${i}]`);
    }
    const params = step.params as Record<string, unknown>;
    const checkParams = (required: string[]) => {
      for (const r of required) {
        if (!(r in params)) {
          throw new Error(`E_SPEC_PARAM_MISSING: steps[${i}].params.${r}`);
        }
      }
      for (const k of Object.keys(params)) {
        if (!required.includes(k)) {
          throw new Error(`E_SPEC_PARAM_EXTRA: steps[${i}].params.${k}`);
        }
      }
    };
    switch (step.op) {
      case "copy": {
        checkParams(["src", "dest"]);
        if (typeof params.src !== "string" || typeof params.dest !== "string") {
          throw new Error(`E_SPEC_PARAM_INVALID: steps[${i}]`);
        }
        break;
      }
      case "create_vm": {
        checkParams(["image", "cpus"]);
        if (
          typeof params.image !== "string" ||
          !Number.isInteger(params.cpus) ||
          (params.cpus as number) < 1
        ) {
          throw new Error(`E_SPEC_PARAM_INVALID: steps[${i}].params.cpus`);
        }
        break;
      }
      case "create_network": {
        checkParams(["cidr"]);
        if (typeof params.cidr !== "string") {
          throw new Error(`E_SPEC_PARAM_INVALID: steps[${i}]`);
        }
        break;
      }
      default:
        throw new Error(`E_SPEC_OP_UNKNOWN: ${step.op}`);
    }
    steps.push({ op: step.op, params });
  }
  return { version: root.version as string, name: root.name as string, steps };
}

export function serializeSpec(spec: TfSpec): Uint8Array {
  return canonicalJsonBytes(spec);
}
