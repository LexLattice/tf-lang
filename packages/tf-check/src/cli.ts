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

const CLI_PATH = fileURLToPath(import.meta.url);

function printHelp(): void {
  process.stdout.write(`${HELP_TEXT}\n`);
}

function printResult(result: ValidationResult): void {
  process.stdout.write(canonicalJson(result));
}

interface FlagDefinition {
  readonly key: string;
  readonly requiresValue: boolean;
}

type ParsedOptions = Partial<Record<string, string>>;

function parseOptions(
  args: string[],
  allowed: Record<string, FlagDefinition>
): ParsedOptions {
  const options: ParsedOptions = {};
  let index = 0;
  while (index < args.length) {
    const arg = args[index];
    index += 1;
    if (!arg.startsWith("--")) {
      throw new Error(`unknown argument: ${arg}`);
    }
    const eqIndex = arg.indexOf("=");
    const flag = eqIndex === -1 ? arg : arg.slice(0, eqIndex);
    const definition = allowed[flag];
    if (!definition) {
      throw new Error(`unknown flag: ${flag}`);
    }
    if (definition.requiresValue) {
      let value = eqIndex === -1 ? undefined : arg.slice(eqIndex + 1);
      if (value === undefined) {
        if (index >= args.length) {
          throw new Error(`missing value for ${flag}`);
        }
        const next = args[index];
        if (next.startsWith("--")) {
          throw new Error(`missing value for ${flag}`);
        }
        value = next;
        index += 1;
      }
      if (!value) {
        throw new Error(`missing value for ${flag}`);
      }
      options[definition.key] = value;
      continue;
    }
    if (eqIndex !== -1) {
      throw new Error(`${flag} does not take a value`);
    }
    options[definition.key] = "true";
  }
  return options;
}

const VALIDATE_FLAGS: Record<string, FlagDefinition> = {
  "--input": { key: "input", requiresValue: true },
  "--out": { key: "out", requiresValue: true },
};

export async function runValidate(args: string[]): Promise<number> {
  try {
    const options = parseOptions(args, VALIDATE_FLAGS);
    const input = options.input;
    if (!input) {
      throw new Error("--input <path> is required");
    }
    const outDir = options.out;
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

const ARTIFACT_FLAGS: Record<string, FlagDefinition> = {
  "--out": { key: "out", requiresValue: true },
};

async function runArtifacts(args: string[]): Promise<number> {
  try {
    const options = parseOptions(args, ARTIFACT_FLAGS);
    const outDir = options.out ?? path.resolve("out/t2/tf-check");
    const selfDir = path.dirname(CLI_PATH);
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

if (process.argv[1] && path.resolve(process.argv[1]) === CLI_PATH) {
  main().catch((error) => {
    process.stderr.write(`${(error as Error).message}\n`);
    exit(2);
  });
}
