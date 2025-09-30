#!/usr/bin/env node
import { readFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { fileURLToPath } from "node:url";
import Ajv from "ajv";
import { parse as parseYaml } from "yaml";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, "..", "..", "..");

const SCHEMAS = {
  l0: path.join(repoRoot, "schemas", "l0-dag.schema.json"),
  l2: path.join(repoRoot, "schemas", "l2-pipeline.schema.json"),
};

function usage() {
  console.error("usage: validate <l0|l2> <file...>");
  process.exit(2);
}

function sanitiseMacroScalars(text) {
  const lines = text.split(/\r?\n/);
  const result = [];

  const countParens = (segment) => {
    const opens = segment.match(/\(/g)?.length ?? 0;
    const closes = segment.match(/\)/g)?.length ?? 0;
    return opens - closes;
  };

  for (let i = 0; i < lines.length; i += 1) {
    const line = lines[i];
    const match = line.match(/^(\s*-\s*[^:\n]+:\s*)(.*)$/);
    if (!match) {
      result.push(line);
      continue;
    }

    const [, prefix, remainder] = match;
    const trimmed = remainder.trim();
    if (
      trimmed.length === 0 ||
      trimmed.startsWith("'") ||
      trimmed.startsWith('"') ||
      trimmed.startsWith("|") ||
      trimmed.startsWith(">")
    ) {
      result.push(line);
      continue;
    }

    if (!trimmed.includes("(")) {
      result.push(line);
      continue;
    }

    let content = trimmed;
    let depth = countParens(content);
    let j = i;
    while (depth > 0 && j + 1 < lines.length) {
      j += 1;
      const nextLine = lines[j];
      const nextTrimmed = nextLine.trim();
      content += ` ${nextTrimmed}`;
      depth += countParens(nextTrimmed);
    }

    const escaped = content.replace(/\\/g, "\\\\").replace(/"/g, '\\"');
    result.push(`${prefix}"${escaped.trim()}"`);
    i = j;
  }

  return result.join("\n");
}

function parseYamlDocument(raw) {
  try {
    return parseYaml(raw);
  } catch (error) {
    if (error?.name !== "YAMLParseError") {
      throw error;
    }
    const sanitised = sanitiseMacroScalars(raw);
    if (sanitised === raw) {
      throw error;
    }
    return parseYaml(sanitised);
  }
}

function parseDocument(targetPath, raw) {
  const ext = path.extname(targetPath).toLowerCase();
  if (ext === ".yaml" || ext === ".yml") {
    return parseYamlDocument(raw);
  }

  try {
    return JSON.parse(raw);
  } catch (error) {
    const hint =
      "Document was not valid JSON. Supply either JSON or YAML with .yml/.yaml extension.";
    throw new Error(`${error?.message ?? error}\n${hint}`);
  }
}

async function loadSchema(schemaKey) {
  const schemaPath = SCHEMAS[schemaKey];
  if (!schemaPath) {
    usage();
  }
  const schemaText = await readFile(schemaPath, "utf8");
  return JSON.parse(schemaText);
}

async function main() {
  let args = process.argv.slice(2);
  if (args[0] === "validate") {
    args = args.slice(1);
  }

  const [schemaKey, ...targets] = args;
  if (!schemaKey || targets.length === 0) {
    usage();
  }

  const schema = await loadSchema(schemaKey);
  const ajv = new Ajv({ allErrors: true, strict: false, allowUnionTypes: true });
  ajv.addFormat("date-time", true);
  const validate = ajv.compile(schema);

  let ok = true;
  for (const target of targets) {
    try {
      const resolved = path.resolve(target);
      const raw = await readFile(resolved, "utf8");
      const document = parseDocument(target, raw);
      const valid = validate(document);
      if (valid) {
        console.log(`${target}: OK`);
      } else {
        ok = false;
        console.error(`${target}: FAIL`);
        for (const error of validate.errors ?? []) {
          const location = error.instancePath ? error.instancePath : "/";
          const message = error.message ?? "invalid";
          console.error(`  - ${location}: ${message}`);
        }
      }
    } catch (err) {
      ok = false;
      const message = err?.message ?? String(err);
      console.error(`${target}: FAIL`);
      for (const line of message.split(/\r?\n/)) {
        console.error(`  - ${line}`);
      }
    }
  }

  process.exit(ok ? 0 : 1);
}

main().catch((err) => {
  console.error(err?.message ?? err);
  process.exit(99);
});
