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
  if (typeof obj !== "object" || obj === null) throw new Error("E_SPEC_TYPE /");
  const root = obj as Record<string, unknown>;
  const allowedRoot = ["version", "name", "steps"];
  for (const k of Object.keys(root)) {
    if (!allowedRoot.includes(k)) throw new Error(`E_SPEC_FIELD_UNKNOWN ${k}`);
  }
  if (root.version !== "0.1") throw new Error("E_SPEC_VERSION version");
  if (typeof root.name !== "string") throw new Error("E_SPEC_NAME name");
  if (!Array.isArray(root.steps)) throw new Error("E_SPEC_STEPS steps");
  const steps: Step[] = [];
  for (let i = 0; i < root.steps.length; i++) {
    const s = root.steps[i] as unknown;
    if (typeof s !== "object" || s === null) throw new Error(`E_SPEC_STEP steps[${i}]`);
    const step = s as Record<string, unknown>;
    if (typeof step.op !== "string") throw new Error(`E_SPEC_OP steps[${i}].op`);
    if (typeof step.params !== "object" || step.params === null) {
      throw new Error(`E_SPEC_PARAMS steps[${i}].params`);
    }
    const params = step.params as Record<string, unknown>;
    const checkNoExtra = (allowed: string[]) => {
      for (const key of Object.keys(params)) {
        if (!allowed.includes(key)) {
          throw new Error(`E_SPEC_PARAM_UNKNOWN steps[${i}].params.${key}`);
        }
      }
    };
    switch (step.op) {
      case "copy":
        if (!("src" in params)) {
          throw new Error(`E_SPEC_PARAM_MISSING steps[${i}].params.src`);
        }
        if (typeof params.src !== "string") {
          throw new Error(`E_SPEC_PARAM_TYPE steps[${i}].params.src`);
        }
        if (!("dest" in params)) {
          throw new Error(`E_SPEC_PARAM_MISSING steps[${i}].params.dest`);
        }
        if (typeof params.dest !== "string") {
          throw new Error(`E_SPEC_PARAM_TYPE steps[${i}].params.dest`);
        }
        checkNoExtra(["src", "dest"]);
        break;
      case "create_vm":
        if (!("image" in params)) {
          throw new Error(`E_SPEC_PARAM_MISSING steps[${i}].params.image`);
        }
        if (typeof params.image !== "string") {
          throw new Error(`E_SPEC_PARAM_TYPE steps[${i}].params.image`);
        }
        if (!("cpus" in params)) {
          throw new Error(`E_SPEC_PARAM_MISSING steps[${i}].params.cpus`);
        }
        if (!Number.isInteger(params.cpus) || (params.cpus as number) < 1) {
          throw new Error(`E_SPEC_PARAM_TYPE steps[${i}].params.cpus`);
        }
        checkNoExtra(["image", "cpus"]);
        break;
      case "create_network":
        if (!("cidr" in params)) {
          throw new Error(`E_SPEC_PARAM_MISSING steps[${i}].params.cidr`);
        }
        if (typeof params.cidr !== "string") {
          throw new Error(`E_SPEC_PARAM_TYPE steps[${i}].params.cidr`);
        }
        checkNoExtra(["cidr"]);
        break;
      default:
        throw new Error(`E_SPEC_OP_UNKNOWN steps[${i}].op`);
    }
    steps.push({ op: step.op, params });
  }
  return { version: root.version as string, name: root.name as string, steps };
}

export function serializeSpec(spec: TfSpec): Uint8Array {
  return canonicalJsonBytes(spec);
}
