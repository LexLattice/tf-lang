import { readFile, writeFile, mkdir } from "node:fs/promises";
import path from "node:path";

export type AllowedOp = "copy" | "create_vm" | "create_network";

export interface CopyStep {
  op: "copy";
  params: { src: string; dest: string };
}

export interface CreateVmStep {
  op: "create_vm";
  params: { image: string; cpus: number };
}

export interface CreateNetworkStep {
  op: "create_network";
  params: { cidr: string };
}

export type Step = CopyStep | CreateVmStep | CreateNetworkStep;

export interface TfSpec {
  version: string;
  name: string;
  steps: Step[];
}

export interface ValidationSource {
  kind: "file" | "inline";
  path?: string;
}

export interface ValidationSummary {
  name: string;
  version: string;
  stepCount: number;
  operations: Record<string, number>;
}

export interface ValidationSuccess {
  status: "ok";
  source: ValidationSource;
  summary: ValidationSummary;
}

export interface ValidationFailure {
  status: "error";
  source: ValidationSource;
  error: {
    code: string;
    path: string;
    message: string;
  };
}

export type ValidationResult = ValidationSuccess | ValidationFailure;

export const HELP_TEXT = `tf-check — validate TF-Lang specs\n\n` +
  `Usage:\n` +
  `  tf-check --help                     Show this message\n` +
  `  tf-check validate --input <path>    Validate a spec file\n` +
  `  tf-check validate --input <path> --out <dir>  Write result.json next to CLI output\n` +
  `  tf-check artifacts [--out <dir>]    Emit canonical help.txt and result.json for CI\n` +
  `\n` +
  `Exit codes:\n` +
  `  0 — validation succeeded\n` +
  `  1 — validation failed (invalid input)\n` +
  `  2 — CLI misuse (missing flags, unknown command)`;

function normalizePath(p: string | undefined): string | undefined {
  if (!p) return undefined;
  const normalized = p.split(path.sep).join("/");
  return normalized === "" ? undefined : normalized;
}

function canonicalize(value: unknown): unknown {
  if (value === null) return null;
  if (Array.isArray(value)) {
    return value.map((item) => canonicalize(item));
  }
  if (typeof value === "object") {
    const entries = Object.entries(value as Record<string, unknown>)
      .map(([k, v]) => [k, canonicalize(v)] as const)
      .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
    const result: Record<string, unknown> = {};
    for (const [k, v] of entries) {
      result[k] = v;
    }
    return result;
  }
  return value;
}

export function canonicalJson(value: unknown): string {
  const canonical = canonicalize(value);
  return `${JSON.stringify(canonical, null, 2)}\n`;
}

function opCounts(spec: TfSpec): Record<string, number> {
  const counts: Record<string, number> = {};
  for (const step of spec.steps) {
    const current = counts[step.op] ?? 0;
    counts[step.op] = current + 1;
  }
  const ordered = Object.keys(counts).sort();
  const result: Record<string, number> = {};
  for (const key of ordered) {
    result[key] = counts[key];
  }
  return result;
}

function summarize(spec: TfSpec): ValidationSummary {
  return {
    name: spec.name,
    version: spec.version,
    stepCount: spec.steps.length,
    operations: opCounts(spec),
  };
}

interface ValidationError {
  code: string;
  path: string;
  message: string;
}

function pointerSegment(segment: string | number): string {
  const raw = typeof segment === "number" ? String(segment) : segment;
  return raw.replace(/~/g, "~0").replace(/\//g, "~1");
}

function pointer(...segments: Array<string | number>): string {
  if (segments.length === 0) return "/";
  return `/${segments.map(pointerSegment).join("/")}`;
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

function parseInput(input: string | Uint8Array | object): unknown {
  if (typeof input === "string") {
    return JSON.parse(input);
  }
  if (input instanceof Uint8Array) {
    return JSON.parse(new TextDecoder().decode(input));
  }
  return input;
}

function fail(code: string, pathStr: string): ValidationError {
  return { code, path: pathStr, message: `${code} ${pathStr}` };
}

function ensureString(value: unknown, code: string, pathStr: string): ValidationError | string {
  if (typeof value !== "string" || value.length === 0) {
    return fail(code, pathStr);
  }
  return value;
}

function ensureInteger(value: unknown, code: string, pathStr: string): ValidationError | number {
  if (typeof value !== "number" || !Number.isInteger(value) || value < 1) {
    return fail(code, pathStr);
  }
  return value;
}

function checkExtraParams(
  params: Record<string, unknown>,
  allowed: string[],
  base: Array<string | number>
): ValidationError | null {
  const allowedSet = new Set(allowed);
  for (const key of Object.keys(params)) {
    if (!allowedSet.has(key)) {
      return fail("E_SPEC_PARAM_UNKNOWN", pointer(...base, "params", key));
    }
  }
  return null;
}

function parseStep(raw: unknown, index: number): { step: Step } | { error: ValidationError } {
  if (!isRecord(raw)) {
    return { error: fail("E_SPEC_STEP", pointer("steps", index)) };
  }
  const opValue = raw.op;
  if (typeof opValue !== "string") {
    return { error: fail("E_SPEC_OP", pointer("steps", index, "op")) };
  }
  if (!isRecord(raw.params)) {
    return { error: fail("E_SPEC_PARAMS", pointer("steps", index, "params")) };
  }
  const params = raw.params;

  switch (opValue as AllowedOp) {
    case "copy": {
      const extra = checkExtraParams(params, ["src", "dest"], ["steps", index]);
      if (extra) return { error: extra };
      const src = ensureString(params.src, "E_SPEC_PARAM_TYPE", pointer("steps", index, "params", "src"));
      if (typeof src !== "string") return { error: src };
      const dest = ensureString(params.dest, "E_SPEC_PARAM_TYPE", pointer("steps", index, "params", "dest"));
      if (typeof dest !== "string") return { error: dest };
      return { step: { op: "copy", params: { src, dest } } };
    }
    case "create_vm": {
      const extra = checkExtraParams(params, ["image", "cpus"], ["steps", index]);
      if (extra) return { error: extra };
      const image = ensureString(params.image, "E_SPEC_PARAM_TYPE", pointer("steps", index, "params", "image"));
      if (typeof image !== "string") return { error: image };
      const cpus = ensureInteger(params.cpus, "E_SPEC_PARAM_TYPE", pointer("steps", index, "params", "cpus"));
      if (typeof cpus !== "number") return { error: cpus };
      return { step: { op: "create_vm", params: { image, cpus } } };
    }
    case "create_network": {
      const extra = checkExtraParams(params, ["cidr"], ["steps", index]);
      if (extra) return { error: extra };
      const cidr = ensureString(params.cidr, "E_SPEC_PARAM_TYPE", pointer("steps", index, "params", "cidr"));
      if (typeof cidr !== "string") return { error: cidr };
      return { step: { op: "create_network", params: { cidr } } };
    }
    default:
      return { error: fail("E_SPEC_OP_UNKNOWN", pointer("steps", index, "op")) };
  }
}

function parseSpecValue(value: unknown): { spec: TfSpec } | { error: ValidationError } {
  if (!isRecord(value)) {
    return { error: fail("E_SPEC_TYPE", "/") };
  }
  const record = value as Record<string, unknown>;
  const version = ensureString(record.version, "E_SPEC_VERSION", "/version");
  if (typeof version !== "string") return { error: version };
  if (version !== "0.1") {
    return { error: fail("E_SPEC_VERSION", "/version") };
  }
  const name = ensureString(record.name, "E_SPEC_NAME", "/name");
  if (typeof name !== "string") return { error: name };
  if (!Array.isArray(record.steps)) {
    return { error: fail("E_SPEC_STEPS", "/steps") };
  }
  const steps: Step[] = [];
  const extraRoot = checkExtraParams(record, ["version", "name", "steps"], []);
  if (extraRoot) {
    return { error: extraRoot };
  }
  for (let i = 0; i < record.steps.length; i += 1) {
    const parsed = parseStep(record.steps[i], i);
    if ("error" in parsed) {
      return { error: parsed.error };
    }
    steps.push(parsed.step);
  }
  return { spec: { version, name, steps } };
}

export function validateSpec(
  input: string | Uint8Array | object,
  source: ValidationSource = { kind: "inline" }
): ValidationResult {
  const data = parseInput(input);
  const parsed = parseSpecValue(data);
  if ("error" in parsed) {
    return {
      status: "error",
      source,
      error: parsed.error,
    };
  }
  return {
    status: "ok",
    source,
    summary: summarize(parsed.spec),
  };
}

export async function validateSpecFile(filePath: string): Promise<ValidationResult> {
  const absolute = path.resolve(filePath);
  const rel = normalizePath(path.relative(process.cwd(), absolute));
  const data = await readFile(absolute, "utf-8");
  return validateSpec(data, { kind: "file", path: rel ?? normalizePath(absolute) });
}

export async function writeResultFile(targetPath: string, result: ValidationResult): Promise<void> {
  await mkdir(path.dirname(targetPath), { recursive: true });
  await writeFile(targetPath, canonicalJson(result), "utf-8");
}

export async function writeHelpFile(targetPath: string): Promise<void> {
  await mkdir(path.dirname(targetPath), { recursive: true });
  await writeFile(targetPath, `${HELP_TEXT}\n`, "utf-8");
}

export interface ArtifactOptions {
  outDir: string;
  inputPath: string;
}

export async function writeArtifacts(options: ArtifactOptions): Promise<void> {
  const { outDir, inputPath } = options;
  const helpPath = path.join(outDir, "help.txt");
  const resultPath = path.join(outDir, "result.json");
  await writeHelpFile(helpPath);
  const result = await validateSpecFile(inputPath);
  await writeResultFile(resultPath, result);
}
