import Ajv from "ajv";
import type { ErrorObject } from "ajv";

import schema from "../../../../schema/tf-spec.schema.json" with { type: "json" };
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

const ajv = new Ajv({ allErrors: true, strict: false });
const validateSpec = ajv.compile(schema);
const ALLOWED_OPS = new Set(["copy", "create_vm", "create_network"]);

function encodePointerSegment(segment: string): string {
  return segment.replace(/~/g, "~0").replace(/\//g, "~1");
}

function appendPointer(path: string, segment?: string): string {
  if (segment === undefined) {
    return path || "/";
  }
  const encoded = encodePointerSegment(segment);
  return `${path || ""}/${encoded}`;
}

function normalizePointer(path: string | undefined): string {
  return path && path.length > 0 ? path : "/";
}

function decodePointerSegment(segment: string): string {
  return segment.replace(/~1/g, "/").replace(/~0/g, "~");
}

function valueAtPointer(root: unknown, pointer: string): unknown {
  if (!pointer || pointer === "/") {
    return root;
  }
  const segments = pointer
    .split("/")
    .slice(1)
    .map(decodePointerSegment);
  let current: unknown = root;
  for (const segment of segments) {
    if (current === null || typeof current !== "object") {
      return undefined;
    }
    current = (current as Record<string, unknown>)[segment];
  }
  return current;
}

function mapError(error: ErrorObject): never {
  const basePath = error.instancePath ?? "";
  const pointer = normalizePointer(basePath);
  const join = (segment?: string) => normalizePointer(appendPointer(basePath, segment));

  const pathMatches = (exp: RegExp) => exp.test(join().slice(1));

  switch (error.keyword) {
    case "additionalProperties": {
      const prop = (error.params as { additionalProperty: string }).additionalProperty;
      const target = appendPointer(basePath, prop);
      const code = basePath ? "E_SPEC_PARAM_UNKNOWN" : "E_SPEC_FIELD_UNKNOWN";
      throw new Error(`${code} ${normalizePointer(target)}`);
    }
    case "required": {
      const missing = (error.params as { missingProperty: string }).missingProperty;
      const target = appendPointer(basePath, missing);
      const normalized = normalizePointer(target);
      if (normalized === "/version") throw new Error("E_SPEC_VERSION /version");
      if (normalized === "/name") throw new Error("E_SPEC_NAME /name");
      if (normalized === "/steps") throw new Error("E_SPEC_STEPS /steps");
      if (/^\/steps\/\d+\/op$/.test(normalized)) throw new Error(`E_SPEC_OP ${normalized}`);
      if (/^\/steps\/\d+\/params$/.test(normalized)) throw new Error(`E_SPEC_PARAMS ${normalized}`);
      throw new Error(`E_SPEC_PARAM_MISSING ${normalized}`);
    }
    case "type": {
      const normalized = normalizePointer(basePath);
      if (normalized === "/") throw new Error("E_SPEC_TYPE /");
      if (normalized === "/version") throw new Error("E_SPEC_VERSION /version");
      if (normalized === "/name") throw new Error("E_SPEC_NAME /name");
      if (normalized === "/steps") throw new Error("E_SPEC_STEPS /steps");
      if (/^\/steps\/\d+$/.test(normalized)) throw new Error(`E_SPEC_STEP ${normalized}`);
      if (/^\/steps\/\d+\/op$/.test(normalized)) throw new Error(`E_SPEC_OP ${normalized}`);
      if (/^\/steps\/\d+\/params$/.test(normalized)) throw new Error(`E_SPEC_PARAMS ${normalized}`);
      if (/^\/steps\/\d+\/params\//.test(normalized)) throw new Error(`E_SPEC_PARAM_TYPE ${normalized}`);
      throw new Error(`E_SPEC_PARAM_TYPE ${normalized}`);
    }
    case "const": {
      const normalized = normalizePointer(basePath);
      if (normalized === "/version") throw new Error("E_SPEC_VERSION /version");
      if (/^\/steps\/\d+\/op$/.test(normalized)) throw new Error(`E_SPEC_OP_UNKNOWN ${normalized}`);
      throw new Error(`E_SPEC_PARAM_TYPE ${normalized}`);
    }
    case "enum": {
      const normalized = normalizePointer(basePath);
      if (normalized === "/version") throw new Error("E_SPEC_VERSION /version");
      if (/^\/steps\/\d+\/op$/.test(normalized)) throw new Error(`E_SPEC_OP_UNKNOWN ${normalized}`);
      throw new Error(`E_SPEC_PARAM_TYPE ${normalized}`);
    }
    case "minimum": {
      const normalized = normalizePointer(basePath);
      throw new Error(`E_SPEC_PARAM_TYPE ${normalized}`);
    }
    default: {
      if (error.keyword === "oneOf") {
        throw new Error(`E_SPEC_OP_UNKNOWN ${normalizePointer(basePath || "/steps")}`);
      }
      if (pathMatches(/^steps\/\d+\/params\//)) {
        throw new Error(`E_SPEC_PARAM_TYPE ${normalizePointer(basePath)}`);
      }
      throw new Error(`E_SPEC_PARAM_TYPE ${normalizePointer(basePath)}`);
    }
  }
}

function parseInput(input: string | Uint8Array | object): unknown {
  if (typeof input === "string") {
    return JSON.parse(input);
  }
  if (input instanceof Uint8Array) {
    return JSON.parse(decoder.decode(input));
  }
  return input;
}

function errorDepth(error: ErrorObject): number {
  const base = error.instancePath ? error.instancePath.split("/").filter(Boolean).length : 0;
  if (error.keyword === "additionalProperties" || error.keyword === "required") {
    return base + 1;
  }
  return base;
}

function keywordScore(keyword: string): number {
  switch (keyword) {
    case "minimum":
    case "type":
      return 6;
    case "required":
    case "additionalProperties":
      return 5;
    case "enum":
      return 4;
    case "const":
      return 3;
    case "oneOf":
      return 1;
    default:
      return 2;
  }
}

function firstRelevantError(errors: ErrorObject[] | null | undefined, root: unknown): ErrorObject {
  if (!errors || errors.length === 0) {
    throw new Error("E_SPEC_TYPE /");
  }
  const prefer = errors.find((err) => {
    const path = err.instancePath ?? "";
    if (err.keyword === "const" || err.keyword === "enum") {
      if (/^\/steps\/\d+\/op$/.test(path)) {
        const value = valueAtPointer(root, path);
        return typeof value === "string" && !ALLOWED_OPS.has(value);
      }
      if (path === "/version") {
        return true;
      }
    }
    return false;
  });
  if (prefer) {
    return prefer;
  }
  const ranked = [...errors].sort((a, b) => {
    const depthDiff = errorDepth(b) - errorDepth(a);
    if (depthDiff !== 0) return depthDiff;
    return keywordScore(b.keyword) - keywordScore(a.keyword);
  });
  return ranked[0];
}

export function parseSpec(input: string | Uint8Array | object): TfSpec {
  const obj = parseInput(input);

  if (!validateSpec(obj)) {
    const error = firstRelevantError(validateSpec.errors ?? undefined, obj);
    mapError(error);
  }

  return obj as unknown as TfSpec;
}

export function serializeSpec(spec: TfSpec): Uint8Array {
  return canonicalJsonBytes(spec);
}
