import { readFile, writeFile, mkdir } from "node:fs/promises";
import path from "node:path";

import { parseSpec as l0ParseSpec, type TfSpec as L0TfSpec } from "tf-lang-l0";

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

type BaseSpec = Omit<L0TfSpec, "steps">;

export interface TfSpec extends BaseSpec {
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

function mapL0Error(error: unknown): { code: string; path: string; message: string } {
  const message = (error instanceof Error ? error.message : String(error)) ?? "";
  const match = message.match(/^(E_SPEC_[A-Z_]+)\s+(\/.*)$/);
  if (match) {
    return { code: match[1], path: match[2], message };
  }
  return { code: "E_SPEC_UNKNOWN", path: "/", message };
}

function coerceSpec(spec: L0TfSpec): TfSpec {
  return spec as unknown as TfSpec;
}

export function validateSpec(
  input: string | Uint8Array | object,
  source: ValidationSource = { kind: "inline" }
): ValidationResult {
  try {
    const parsed = coerceSpec(l0ParseSpec(input));
    return {
      status: "ok",
      source,
      summary: summarize(parsed),
    };
  } catch (error) {
    return {
      status: "error",
      source,
      error: mapL0Error(error),
    };
  }
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
