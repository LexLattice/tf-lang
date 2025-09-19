#!/usr/bin/env node
import fs from "fs-extra";
import path from "node:path";
import process from "node:process";
import { replay, SliceSpec } from "./index.js";

interface CliArgs {
  input: string;
  seed: number;
  slice?: SliceSpec;
  out: string;
}

function parseSlice(value: string | undefined): SliceSpec | undefined {
  if (!value) return undefined;
  const [startStr = "0", endStr, stepStr = "1"] = value.split(":");
  const start = Number(startStr);
  const end = endStr === undefined || endStr === "" ? undefined : Number(endStr);
  const step = Number(stepStr);
  if (!Number.isInteger(start) || (end !== undefined && !Number.isInteger(end)) || !Number.isInteger(step)) {
    throw new Error(`Invalid slice spec: ${value}`);
  }
  return { start, end, step };
}

function parseArgs(argv: string[]): CliArgs {
  const maybeCommand = argv[2];
  const commandIsOption = maybeCommand?.startsWith("--");
  const command = commandIsOption ? "replay" : maybeCommand ?? "replay";
  if (command !== "replay") {
    throw new Error(`Unknown command: ${command}`);
  }
  const startIndex = commandIsOption ? 2 : 3;
  const args: Record<string, string> = {};
  for (let i = startIndex; i < argv.length; i += 2) {
    const key = argv[i];
    const value = argv[i + 1];
    if (!key || !value) {
      throw new Error("Arguments must be provided as --key value pairs");
    }
    if (!key.startsWith("--")) {
      throw new Error(`Unexpected argument: ${key}`);
    }
    args[key.slice(2)] = value;
  }
  if (!args.input) throw new Error("--input is required");
  if (!args.seed) throw new Error("--seed is required");
  if (!args.out) throw new Error("--out is required");
  const slice = parseSlice(args.slice);
  return {
    input: path.resolve(args.input),
    seed: Number(args.seed),
    out: path.resolve(args.out),
    slice,
  };
}

async function main() {
  try {
    const options = parseArgs(process.argv);
    const frames = await replay(options);
    await fs.ensureDir(path.dirname(options.out));
    const ndjson = frames.map((frame) => JSON.stringify(frame)).join("\n");
    await fs.writeFile(options.out, ndjson + (frames.length > 0 ? "\n" : ""), "utf8");
  } catch (error) {
    console.error(error instanceof Error ? error.message : error);
    process.exitCode = 1;
  }
}

await main();
