import { canonicalJsonBytes } from "../canon/json.js";

export interface Step {
  op: string;
  params: Record<string, string | number | boolean>;
}

export interface TfSpec {
  version: string;
  name: string;
  steps: Step[];
}

export function parseSpec(input: string | Uint8Array | object): TfSpec {
  let obj: unknown;
  if (typeof input === "string") {
    obj = JSON.parse(input);
  } else if (input instanceof Uint8Array) {
    obj = JSON.parse(new TextDecoder().decode(input));
  } else {
    obj = input;
  }
  if (typeof obj !== "object" || obj === null) throw new Error("E_SPEC_TYPE");
  const root = obj as Record<string, unknown>;
  for (const k of Object.keys(root)) {
    if (!{"version": 1, "name": 1, "steps": 1}[k]) throw new Error("E_SPEC_FIELD");
  }
  if (root.version !== "0.1") throw new Error("E_SPEC_VERSION");
  if (typeof root.name !== "string") throw new Error("E_SPEC_NAME");
  if (!Array.isArray(root.steps) || root.steps.length === 0) throw new Error("E_SPEC_STEPS");
  const steps = (root.steps as unknown[]).map(s => {
    if (typeof s !== "object" || s === null) throw new Error("E_SPEC_STEP");
    const step = s as Record<string, unknown>;
    for (const k of Object.keys(step)) {
      if (!{"op": 1, "params": 1}[k]) throw new Error("E_SPEC_STEP_FIELD");
    }
    if (typeof step.op !== "string") throw new Error("E_SPEC_OP");
    if (typeof step.params !== "object" || step.params === null) throw new Error("E_SPEC_PARAMS");
    const params = step.params as Record<string, string | number | boolean>;
    for (const v of Object.values(params)) {
      if (typeof v !== "string" && typeof v !== "number" && typeof v !== "boolean") {
        throw new Error("E_SPEC_PARAM_TYPE");
      }
    }
    return { op: step.op as string, params };
  });
  return { version: root.version as string, name: root.name as string, steps };
}

export function serializeSpec(spec: TfSpec): Uint8Array {
  return canonicalJsonBytes(spec);
}
