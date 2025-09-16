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

function parseFlags(
  args: string[],
  allowed: readonly string[]
): Record<string, string> {
  const allowedSet = new Set(allowed);
  const values: Record<string, string> = {};
  let index = 0;
  while (index < args.length) {
    const token = args[index];
    if (!token.startsWith("--")) {
      throw new Error(`unexpected argument: ${token}`);
    }
    const equals = token.indexOf("=");
    const flag = equals === -1 ? token : token.slice(0, equals);
    if (!allowedSet.has(flag)) {
      throw new Error(`unknown flag: ${flag}`);
    }
    let value: string;
    if (equals !== -1) {
      value = token.slice(equals + 1);
      if (value.length === 0) {
        throw new Error(`missing value for ${flag}`);
      }
    } else {
      const next = args[index + 1];
      if (!next || next.startsWith("--")) {
        throw new Error(`missing value for ${flag}`);
      }
      value = next;
      index += 1;
    }
    values[flag] = value;
    index += 1;
  }
  return values;
}

async function runValidate(args: string[]): Promise<number> {
  try {
    const flags = parseFlags(args, ["--input", "--out"]);
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

async function runArtifacts(args: string[]): Promise<number> {
  try {
    const flags = parseFlags(args, ["--out"]);
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

export async function runCli(argv: string[]): Promise<number> {
  if (argv.length === 0 || argv.includes("--help") || argv.includes("-h")) {
    printHelp();
    return 0;
  }
  const [command, ...rest] = argv;
  switch (command) {
    case "validate":
      return runValidate(rest);
    case "artifacts":
      return runArtifacts(rest);
    default:
      process.stderr.write(`unknown command: ${command}\n`);
      printHelp();
      return 2;
  }
}

async function main(): Promise<void> {
  const exitCode = await runCli(process.argv.slice(2));
  exit(exitCode);
}

const invoked = process.argv[1]
  ? new URL(process.argv[1], "file://").href
  : undefined;

if (invoked === import.meta.url) {
  main().catch((error) => {
    process.stderr.write(`${(error as Error).message}\n`);
    exit(2);
  });
}
