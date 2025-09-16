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

function printHelp(): void {
  process.stdout.write(`${HELP_TEXT}\n`);
}

function printResult(result: ValidationResult): void {
  process.stdout.write(canonicalJson(result));
}

function parseFlagArgs(
  args: string[],
  allowedFlags: string[]
): Partial<Record<string, string>> {
  const allowed = new Set(allowedFlags);
  const values: Partial<Record<string, string>> = {};
  let index = 0;
  while (index < args.length) {
    const token = args[index];
    if (!token.startsWith("--")) {
      throw new Error(`unknown flag: ${token}`);
    }
    const [flag, inline] = token.split("=", 2);
    if (!allowed.has(flag)) {
      throw new Error(`unknown flag: ${flag}`);
    }
    if (inline !== undefined) {
      if (inline.length === 0) {
        throw new Error(`missing value for ${flag}`);
      }
      values[flag] = inline;
      index += 1;
      continue;
    }
    const next = args[index + 1];
    if (!next || next.startsWith("--")) {
      throw new Error(`missing value for ${flag}`);
    }
    values[flag] = next;
    index += 2;
  }
  return values;
}

export async function runValidate(args: string[]): Promise<number> {
  try {
    const flags = parseFlagArgs(args, ["--input", "--out"]);
    const input = flags["--input"];
    if (!input) {
      throw new Error("--input <path> is required");
    }
    const outDir = flags["--out"];
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
    const flags = parseFlagArgs(args, ["--out"]);
    const outDir = flags["--out"] ?? path.resolve("out/t2/tf-check");
    const selfDir = path.dirname(fileURLToPath(import.meta.url));
    const sample = path.join(selfDir, "../fixtures/sample-spec.json");
    await writeArtifacts({ outDir, inputPath: sample });
    const result = await validateSpecFile(sample);
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

main().catch((error) => {
  process.stderr.write(`${(error as Error).message}\n`);
  exit(2);
});
