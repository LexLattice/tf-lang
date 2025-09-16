#!/usr/bin/env node
import path from "node:path";
import { exit } from "node:process";
import { fileURLToPath } from "node:url";

import {
  HELP_TEXT,
  validateSpecFile,
  writeResultFile,
  writeArtifacts,
  canonicalJson,
  type ValidationResult,
} from "./index.js";
import { findRepoRoot } from "@tf-lang/utils";

const cliDir = path.dirname(fileURLToPath(import.meta.url));
const sampleSpecPath = path.join(cliDir, "../fixtures/sample-spec.json");

let cachedArtifactsDir: string | undefined;
function resolveDefaultArtifactsDir(
  resolver: (dir: string) => string = findRepoRoot
): string {
  if (cachedArtifactsDir) {
    return cachedArtifactsDir;
  }
  try {
    const repoRoot = resolver(cliDir);
    cachedArtifactsDir = path.join(repoRoot, "out/t2/tf-check");
  } catch {
    cachedArtifactsDir = path.resolve("out/t2/tf-check");
  }
  return cachedArtifactsDir;
}

function resetArtifactsDirCache(): void {
  cachedArtifactsDir = undefined;
}

function printHelp(): void {
  process.stdout.write(`${HELP_TEXT}\n`);
}

function printResult(result: ValidationResult): void {
  process.stdout.write(canonicalJson(result));
}

type ParsedFlags = {
  values: Partial<Record<string, string>>;
  toggles: Set<string>;
};

function parseFlagArgs(
  args: string[],
  valueFlags: string[],
  toggleFlags: string[] = []
): ParsedFlags {
  const valueSet = new Set(valueFlags);
  const toggleSet = new Set(toggleFlags);
  const values: Partial<Record<string, string>> = {};
  const toggles = new Set<string>();
  let index = 0;
  while (index < args.length) {
    const token = args[index];
    if (!token.startsWith("-")) {
      throw new Error(`unknown flag: ${token}`);
    }
    if (toggleSet.has(token)) {
      toggles.add(token);
      index += 1;
      continue;
    }
    if (!token.startsWith("--")) {
      throw new Error(`unknown flag: ${token}`);
    }
    const [flag, inline] = token.split("=", 2);
    if (toggleSet.has(flag)) {
      if (inline !== undefined) {
        throw new Error(`flag ${flag} does not take a value`);
      }
      toggles.add(flag);
      index += 1;
      continue;
    }
    if (!valueSet.has(flag)) {
      throw new Error(`unknown flag: ${flag}`);
    }
    if (inline !== undefined) {
      values[flag] = inline;
      index += 1;
      continue;
    }
    const next = args[index + 1];
    if (next === undefined || next.startsWith("--")) {
      throw new Error(`missing value for ${flag}`);
    }
    values[flag] = next;
    index += 2;
  }
  return { values, toggles };
}

export async function runValidate(args: string[]): Promise<number> {
  try {
    const parsed = parseFlagArgs(args, ["--input", "--out"], ["--help", "-h"]);
    if (parsed.toggles.has("--help") || parsed.toggles.has("-h")) {
      process.stdout.write(
        "Usage: tf-check validate --input <path> [--out <dir>]\n"
      );
      return 0;
    }
    const input = parsed.values["--input"];
    if (!input) {
      throw new Error("--input <path> is required");
    }
    const outDir = parsed.values["--out"];
    const result = await validateSpecFile(input);
    if (outDir) {
      const outputPath = path.join(outDir, "result.json");
      await writeResultFile(outputPath, result);
    }
    printResult(result);
    return result.status === "ok" ? 0 : 1;
  } catch (error) {
    process.stderr.write(`${(error as Error).message}\n`);
    return 2;
  }
}

export async function runArtifacts(args: string[]): Promise<number> {
  try {
    const parsed = parseFlagArgs(args, ["--out"], ["--help", "-h"]);
    if (parsed.toggles.has("--help") || parsed.toggles.has("-h")) {
      process.stdout.write(
        "Usage: tf-check artifacts [--out <dir>]\n"
      );
      return 0;
    }
    const outDir = parsed.values["--out"] ?? resolveDefaultArtifactsDir();
    await writeArtifacts({ outDir, inputPath: sampleSpecPath });
    const result = await validateSpecFile(sampleSpecPath);
    printResult(result);
    return result.status === "ok" ? 0 : 1;
  } catch (error) {
    process.stderr.write(`${(error as Error).message}\n`);
    return 2;
  }
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes("--help") || args.includes("-h")) {
    printHelp();
    exit(0);
  }
  const command = args[0];
  const rest = args.slice(1);
  switch (command) {
    case "validate": {
      const exitCode = await runValidate(rest);
      exit(exitCode);
      return;
    }
    case "artifacts": {
      const exitCode = await runArtifacts(rest);
      exit(exitCode);
      return;
    }
    default: {
      process.stderr.write(`unknown command: ${command}\n`);
      printHelp();
      exit(2);
    }
  }
}

if (!process.env.VITEST) {
  main().catch((error) => {
    process.stderr.write(`${(error as Error).message}\n`);
    exit(2);
  });
}

export { parseFlagArgs, resolveDefaultArtifactsDir, resetArtifactsDirCache };
