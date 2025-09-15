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
  if (root.version !== "0.1") throw new Error("E_SPEC_VERSION /version");
  if (typeof root.name !== "string") throw new Error("E_SPEC_NAME /name");
  if (!Array.isArray(root.steps)) throw new Error("E_SPEC_STEPS /steps");
  const stepArr = root.steps as unknown[];
  const steps: Step[] = [];
  for (let i = 0; i < stepArr.length; i++) {
    const s = stepArr[i];
    if (typeof s !== "object" || s === null) throw new Error(`E_SPEC_STEP /steps/${i}`);
    const step = s as Record<string, unknown>;
    if (typeof step.op !== "string") throw new Error(`E_SPEC_OP /steps/${i}/op`);
    if (typeof step.params !== "object" || step.params === null || Array.isArray(step.params)) {
      throw new Error(`E_SPEC_PARAMS /steps/${i}/params`);
    }
    if (Object.keys(step).length !== 2) {
      throw new Error(`E_SPEC_STEP /steps/${i}`);
    }
    const params = step.params as Record<string, unknown>;
    switch (step.op) {
      case "copy":
        if (typeof params.src !== "string") {
          throw new Error(`E_SPEC_PARAM /steps/${i}/params/src`);
        }
        if (typeof params.dest !== "string") {
          throw new Error(`E_SPEC_PARAM /steps/${i}/params/dest`);
        }
        if (Object.keys(params).length !== 2) {
          throw new Error(`E_SPEC_PARAM /steps/${i}/params`);
        }
        break;
      case "create_vm":
        if (typeof params.image !== "string") {
          throw new Error(`E_SPEC_PARAM /steps/${i}/params/image`);
        }
        if (typeof params.cpus !== "number" || !Number.isInteger(params.cpus) || params.cpus < 1) {
          throw new Error(`E_SPEC_PARAM /steps/${i}/params/cpus`);
        }
        if (Object.keys(params).length !== 2) {
          throw new Error(`E_SPEC_PARAM /steps/${i}/params`);
        }
        break;
      case "create_network":
        if (typeof params.cidr !== "string") {
          throw new Error(`E_SPEC_PARAM /steps/${i}/params/cidr`);
        }
        if (Object.keys(params).length !== 1) {
          throw new Error(`E_SPEC_PARAM /steps/${i}/params`);
        }
        break;
      default:
        throw new Error(`E_SPEC_OP_UNKNOWN /steps/${i}/op`);
    }
    steps.push({ op: step.op, params });
  }
  return { version: root.version as string, name: root.name as string, steps };
}

export function serializeSpec(spec: TfSpec): Uint8Array {
  return canonicalJsonBytes(spec);
}
