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
  if (root.version !== "0.1") throw new Error("E_SPEC_VERSION");
  if (typeof root.name !== "string") throw new Error("E_SPEC_NAME");
  if (!Array.isArray(root.steps)) throw new Error("E_SPEC_STEPS");
  const steps: Step[] = [];
  for (const s of root.steps as unknown[]) {
    if (typeof s !== "object" || s === null) throw new Error("E_SPEC_STEP");
    const step = s as Record<string, unknown>;
    if (typeof step.op !== "string") throw new Error("E_SPEC_OP");
    if (typeof step.params !== "object" || step.params === null) {
      throw new Error("E_SPEC_PARAMS");
    }
    const params = step.params as Record<string, unknown>;
    switch (step.op) {
      case "copy":
        if (typeof params.src !== "string" || typeof params.dest !== "string") {
          throw new Error("E_SPEC_PARAM");
        }
        break;
      case "create_vm":
        if (typeof params.image !== "string" || !Number.isInteger(params.cpus)) {
          throw new Error("E_SPEC_PARAM");
        }
        break;
      case "create_network":
        if (typeof params.cidr !== "string") {
          throw new Error("E_SPEC_PARAM");
        }
        break;
      default:
        throw new Error("E_SPEC_OP_UNKNOWN");
    }
    steps.push({ op: step.op, params });
  }
  return { version: root.version as string, name: root.name as string, steps };
}

export function serializeSpec(spec: TfSpec): Uint8Array {
  return canonicalJsonBytes(spec);
}
