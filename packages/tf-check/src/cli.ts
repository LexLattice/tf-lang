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

type FlagDefinition = {
  key: string;
  takesValue: boolean;
};

type ParsedFlags = Record<string, string | true | undefined>;

const VALIDATE_FLAGS: Record<string, FlagDefinition> = {
  "--input": { key: "input", takesValue: true },
  "--out": { key: "out", takesValue: true },
};

const ARTIFACT_FLAGS: Record<string, FlagDefinition> = {
  "--out": { key: "out", takesValue: true },
};

function parseFlags(args: string[], spec: Record<string, FlagDefinition>): ParsedFlags {
  const result: ParsedFlags = {};
  let index = 0;
  while (index < args.length) {
    const raw = args[index];
    index += 1;
    if (!raw.startsWith("--")) {
      throw new Error(`unknown flag: ${raw}`);
    }
    const [flag, inline] = raw.split("=", 2);
    const definition = spec[flag];
    if (!definition) {
      throw new Error(`unknown flag: ${flag}`);
    }
    if (definition.takesValue) {
      let value = inline;
      if (value === undefined) {
        if (index >= args.length) {
          throw new Error(`missing value for ${flag}`);
        }
        value = args[index];
        index += 1;
      }
      if (!value || value.startsWith("-")) {
        throw new Error(`missing value for ${flag}`);
      }
      result[definition.key] = value;
    } else {
      if (inline !== undefined) {
        throw new Error(`flag ${flag} does not take a value`);
      }
      result[definition.key] = true;
    }
  }
  return result;
}

export async function runValidate(args: string[]): Promise<number> {
  try {
    const flags = parseFlags(args, VALIDATE_FLAGS);
    const input = flags.input;
    if (typeof input !== "string" || input.length === 0) {
      throw new Error("--input <path> is required");
    }
    const outDir = typeof flags.out === "string" ? flags.out : undefined;
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
    const flags = parseFlags(args, ARTIFACT_FLAGS);
    const outDirValue = typeof flags.out === "string" ? flags.out : undefined;
    const outDir = outDirValue ?? path.resolve("out/t2/tf-check");
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

const invokedPath = process.argv[1] ? path.resolve(process.argv[1]) : null;
const currentPath = path.resolve(fileURLToPath(import.meta.url));
if (invokedPath === currentPath) {
  main().catch((error) => {
    process.stderr.write(`${(error as Error).message}\n`);
    exit(2);
  });
}
