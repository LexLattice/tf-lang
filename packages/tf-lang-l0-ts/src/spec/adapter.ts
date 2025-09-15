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

function err(code: string, path: string, msg: string): never {
  throw new Error(`${code} at ${path}: ${msg}`);
}

export function parseSpec(input: string | Uint8Array | object): TfSpec {
  let obj: unknown;
  if (typeof input === "string") {
    obj = JSON.parse(input);
  } else if (input instanceof Uint8Array) {
    obj = JSON.parse(decoder.decode(input));
  } else {
    obj = input;
  }
  if (typeof obj !== "object" || obj === null || Array.isArray(obj)) {
    err("E_SPEC_TYPE", "", "spec must be an object");
  }
  const root = obj as Record<string, unknown>;
  const allowedRoot = new Set(["version", "name", "steps"]);
  for (const k of Object.keys(root)) {
    if (!allowedRoot.has(k)) err("E_SPEC_EXTRA", k, "unexpected field");
  }
  if (root.version !== "0.1") {
    err("E_SPEC_VERSION", "version", `expected \"0.1\", got ${root.version}`);
  }
  if (typeof root.name !== "string") err("E_SPEC_NAME", "name", "must be string");
  if (!Array.isArray(root.steps)) err("E_SPEC_STEPS", "steps", "must be array");
  const steps: Step[] = [];
  for (const [i, s] of (root.steps as unknown[]).entries()) {
    const spath = `steps[${i}]`;
    if (typeof s !== "object" || s === null || Array.isArray(s)) {
      err("E_SPEC_STEP", spath, "must be object");
    }
    const step = s as Record<string, unknown>;
    const allowedStep = new Set(["op", "params"]);
    for (const k of Object.keys(step)) {
      if (!allowedStep.has(k)) err("E_SPEC_EXTRA", `${spath}.${k}`, "unexpected field");
    }
    if (typeof step.op !== "string") err("E_SPEC_OP", `${spath}.op`, "must be string");
    if (typeof step.params !== "object" || step.params === null || Array.isArray(step.params)) {
      err("E_SPEC_PARAMS", `${spath}.params`, "must be object");
    }
    const params = step.params as Record<string, unknown>;
    const paramPath = `${spath}.params`;
    switch (step.op) {
      case "copy": {
        const required = ["src", "dest"];
        for (const r of required) {
          if (typeof params[r] !== "string") {
            err("E_SPEC_PARAM", `${paramPath}.${r}`, "must be string");
          }
        }
        for (const k of Object.keys(params)) {
          if (!required.includes(k)) {
            err("E_SPEC_PARAM", `${paramPath}.${k}`, "unexpected param");
          }
        }
        break;
      }
      case "create_vm": {
        const required = ["image", "cpus"];
        if (typeof params.image !== "string") {
          err("E_SPEC_PARAM", `${paramPath}.image`, "must be string");
        }
        if (!Number.isInteger(params.cpus) || (params.cpus as number) < 1) {
          err("E_SPEC_PARAM", `${paramPath}.cpus`, "must be integer >=1");
        }
        for (const k of Object.keys(params)) {
          if (!required.includes(k)) {
            err("E_SPEC_PARAM", `${paramPath}.${k}`, "unexpected param");
          }
        }
        break;
      }
      case "create_network": {
        const required = ["cidr"];
        if (typeof params.cidr !== "string") {
          err("E_SPEC_PARAM", `${paramPath}.cidr`, "must be string");
        }
        for (const k of Object.keys(params)) {
          if (!required.includes(k)) {
            err("E_SPEC_PARAM", `${paramPath}.${k}`, "unexpected param");
          }
        }
        break;
      }
      default:
        err("E_SPEC_OP_UNKNOWN", `${spath}.op`, `unknown op ${step.op}`);
    }
    steps.push({ op: step.op, params });
  }
  return { version: root.version as string, name: root.name as string, steps };
}

export function serializeSpec(spec: TfSpec): Uint8Array {
  return canonicalJsonBytes(spec);
}
