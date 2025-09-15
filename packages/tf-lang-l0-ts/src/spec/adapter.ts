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

export function parseSpec(input: string | Uint8Array | object): TfSpec {
  const obj =
    typeof input === "string"
      ? JSON.parse(input)
      : input instanceof Uint8Array
      ? JSON.parse(new TextDecoder().decode(input))
      : input;
  if (typeof obj !== "object" || obj === null) throw new Error("E_SPEC_TYPE");
  const root = obj as Record<string, unknown>;
  if (root.version !== "0.1") throw new Error("E_SPEC_VERSION");
  if (typeof root.name !== "string") throw new Error("E_SPEC_NAME");
  if (!Array.isArray(root.steps)) throw new Error("E_SPEC_STEPS");
  const steps = (root.steps as unknown[]).map(s => {
    if (typeof s !== "object" || s === null) throw new Error("E_SPEC_STEP");
    const step = s as Record<string, unknown>;
    if (typeof step.op !== "string") throw new Error("E_SPEC_OP");
    if (typeof step.params !== "object" || step.params === null)
      throw new Error("E_SPEC_PARAMS");
    return { op: step.op as string, params: step.params as Record<string, unknown> };
  });
  return { version: root.version as string, name: root.name as string, steps };
}

export function serializeSpec(spec: TfSpec): Uint8Array {
  return canonicalJsonBytes(spec);
}
