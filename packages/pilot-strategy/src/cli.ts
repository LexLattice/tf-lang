#!/usr/bin/env node
import path from "node:path";
import process from "node:process";
import { listStrategies, runStrategy, StrategyName } from "./index.js";

interface CliArgs {
  strategy: StrategyName;
  frames: string;
  seed: number;
  out: string;
}

function parseArgs(argv: string[]): CliArgs {
  const maybeCommand = argv[2];
  const commandIsOption = maybeCommand?.startsWith("--");
  const command = commandIsOption ? "run" : maybeCommand ?? "run";
  if (command !== "run") {
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
  if (!args.strategy) {
    throw new Error(`--strategy is required. Available: ${listStrategies().join(", ")}`);
  }
  if (!args.frames) throw new Error("--frames is required");
  if (!args.seed) throw new Error("--seed is required");
  if (!args.out) throw new Error("--out is required");
  return {
    strategy: args.strategy as StrategyName,
    frames: path.resolve(args.frames),
    seed: Number(args.seed),
    out: path.resolve(args.out),
  };
}

async function main() {
  try {
    const args = parseArgs(process.argv);
    await runStrategy({
      strategy: args.strategy,
      framesPath: args.frames,
      seed: args.seed,
      out: args.out,
    });
  } catch (error) {
    console.error(error instanceof Error ? error.message : error);
    process.exitCode = 1;
  }
}

await main();
