#!/usr/bin/env node
import { execFileSync } from "node:child_process";
import { appendFileSync } from "node:fs";

function parseArgs(argv) {
  const args = {};
  for (let i = 0; i < argv.length; i += 2) {
    const key = argv[i];
    const value = argv[i + 1];
    if (!key?.startsWith("--")) {
      throw new Error(`Unexpected argument order at '${key}'`);
    }
    args[key.slice(2)] = value ?? "";
  }
  return args;
}

const { from, to, event, defaultRange } = parseArgs(process.argv.slice(2));
if (!to) throw new Error("Missing --to sha");

let diffFrom = from;
if (!diffFrom) {
  diffFrom = defaultRange || `${to}^`;
}

const diff = execFileSync("git", ["diff", "--name-only", diffFrom, to], { encoding: "utf8" }).trim();
const files = diff ? diff.split(/\r?\n/) : [];

const match = (pattern) => files.filter((file) => pattern.test(file));
const l0Changed = match(/\.l0\.(json|ya?ml)$/);
const l2Changed = match(/\.l2\.(json|ya?ml)$/);
const schemaChanged = match(/^(schemas\/|tools\/tf-lang-cli\/|spec\/v0\.6\/)/);

let l0Targets = l0Changed;
let l2Targets = l2Changed;

if (schemaChanged.length > 0) {
  const allL0 = execFileSync("git", ["ls-files", "**/*.l0.json", "**/*.l0.yaml", "**/*.l0.yml"], { encoding: "utf8" }).trim();
  const allL2 = execFileSync("git", ["ls-files", "**/*.l2.json", "**/*.l2.yaml", "**/*.l2.yml"], { encoding: "utf8" }).trim();
  l0Targets = allL0 ? allL0.split(/\r?\n/) : [];
  l2Targets = allL2 ? allL2.split(/\r?\n/) : [];
}

if (event === "push" && l0Targets.length === 0 && l2Targets.length === 0 && schemaChanged.length === 0) {
  const allL0 = execFileSync("git", ["ls-files", "**/*.l0.json", "**/*.l0.yaml", "**/*.l0.yml"], { encoding: "utf8" }).trim();
  const allL2 = execFileSync("git", ["ls-files", "**/*.l2.json", "**/*.l2.yaml", "**/*.l2.yml"], { encoding: "utf8" }).trim();
  l0Targets = allL0 ? allL0.split(/\r?\n/) : [];
  l2Targets = allL2 ? allL2.split(/\r?\n/) : [];
}

const output = process.env.GITHUB_OUTPUT;
if (!output) throw new Error("GITHUB_OUTPUT is not defined");

function write(name, values) {
  appendFileSync(output, `${name}<<EOF\n${values.join("\n")}\nEOF\n`);
}

write("l0_changed", l0Changed);
write("l2_changed", l2Changed);
write("l0_targets", l0Targets);
write("l2_targets", l2Targets);
