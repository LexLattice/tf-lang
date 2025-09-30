#!/usr/bin/env node
import fs from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { spawnSync, execSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import Ajv from "ajv";

import { loadRulebookPlan, rulesForPhaseFromPlan } from "./expand.mjs";
import { summarizeEffects } from "./lib/effects.mjs";
import { buildDotGraph } from "./lib/dot.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, "..", "..");

const schemaPaths = {
  l0: path.join(repoRoot, "schemas", "l0-dag.schema.json"),
  l2: path.join(repoRoot, "schemas", "l2-pipeline.schema.json")
};

const ajv = new Ajv({ allErrors: true, strict: false, allowUnionTypes: true });
ajv.addFormat("date-time", true);
const validatorCache = new Map();

async function loadJsonFile(targetPath) {
  const filePath = path.resolve(targetPath);
  const content = await readFile(filePath, "utf8");
  return JSON.parse(content);
}

function inferKindFromFile(filePath) {
  if (filePath.endsWith(".l0.json")) return "l0";
  if (filePath.endsWith(".l2.json")) return "l2";
  return null;
}

async function ensureValidator(kind) {
  if (!schemaPaths[kind]) throw new Error(`unknown schema kind: ${kind}`);
  if (!validatorCache.has(kind)) {
    const schema = await loadJsonFile(schemaPaths[kind]);
    const validate = ajv.compile(schema);
    validatorCache.set(kind, validate);
  }
  return validatorCache.get(kind);
}

async function runValidateCommand(args) {
  const argv = [...args];
  let explicitKind = null;
  if (argv[0] && ["l0", "l2"].includes(argv[0])) {
    explicitKind = argv.shift();
  }
  if (argv.length === 0) {
    console.error("usage: tf validate [l0|l2] <FILE...>");
    return 2;
  }

  let exitCode = 0;
  for (const file of argv) {
    const kind = explicitKind ?? inferKindFromFile(file);
    if (!kind) {
      console.error(`${file}: unable to infer schema; pass l0 or l2 explicitly`);
      exitCode = 2; // usage error takes precedence
      continue;
    }

    let doc;
    try {
      doc = await loadJsonFile(file);
    } catch (err) {
      console.error(`${file}: ${err?.message ?? err}`);
      if (exitCode === 0) exitCode = 1;
      continue;
    }

    const validate = await ensureValidator(kind);
    const valid = validate(doc);
    if (!valid) {
      const message = ajv.errorsText(validate.errors, { separator: "\n  - " });
      console.error(`${file}: validation failed [${kind}]\n  - ${message}`);
      if (exitCode === 0) exitCode = 1;
    } else {
      console.log(`${file}: OK [${kind}]`);
    }
  }
  return exitCode;
}

async function runEffectsCommand(file) {
  if (!file) {
    console.error("usage: tf effects <FILE>");
    return 2;
  }
  try {
    const doc = await loadJsonFile(file);
    const summary = summarizeEffects(doc);
    console.log(summary);
    return 0;
  } catch (err) {
    console.error(`${file}: ${err?.message ?? err}`);
    return 1;
  }
}

async function runGraphCommand(rawArgs) {
  const argv = Array.isArray(rawArgs) ? [...rawArgs] : rawArgs !== undefined ? [rawArgs] : [];
  let strictGraph = true;
  const files = [];

  for (const arg of argv) {
    if (arg === "--strict-graph") { strictGraph = true; continue; }
    if (arg === "--no-strict-graph") { strictGraph = false; continue; }
    const match = /^--strict-graph=(.+)$/u.exec(arg);
    if (match) {
      const value = match[1].toLowerCase();
      strictGraph = !["false", "0", "no", "off"].includes(value);
      continue;
    }
    files.push(arg);
  }

  if (files.length !== 1) {
    console.error("usage: tf graph [--strict-graph[=true|false]] <FILE>");
    return 2;
  }

  const [file] = files;
  try {
    const doc = await loadJsonFile(file);
    const dot = buildDotGraph(doc, { strict: strictGraph });
    console.log(dot);
    return 0;
  } catch (err) {
    console.error(`${file}: ${err?.message ?? err}`);
    return 1;
  }
}

function rbPath(node) {
  const p = path.join("tf", "blocks", node, "rulebook.yml");
  if (!fs.existsSync(p)) throw new Error(`missing rulebook: ${p}`);
  return p;
}

function resolveRulebookPath(input) {
  if (!input) return null;
  if (input.includes("/") || input.endsWith(".yml") || input.endsWith(".yaml")) {
    if (!fs.existsSync(input)) throw new Error(`missing rulebook: ${input}`);
    return input;
  }
  return rbPath(input);
}

function writeDiff(text) {
  fs.mkdirSync("out/tmp", { recursive: true });
  const p = "out/tmp/latest.diff";
  fs.writeFileSync(p, text, "utf8");
  return path.resolve(p);
}

function run(cmd, env) {
  const r = spawnSync(cmd, {
    shell: true,
    encoding: "utf8",
    env: { ...process.env, ...env },
    maxBuffer: 10 * 1024 * 1024
  });
  return { code: r.status ?? 99, stdout: (r.stdout || "").trim(), stderr: (r.stderr || "").trim() };
}

function check(res, expect) {
  if (!expect) return { ok: res.code === 0 };
  if (expect.code !== undefined && res.code !== expect.code) return { ok: false };
  if (expect.exit_code !== undefined && res.code !== expect.exit_code) return { ok: false };
  if (expect.contains) {
    const out = `${res.stdout}\n${res.stderr}`;
    if (!out.includes(expect.contains)) return { ok: false };
  }
  if (expect.ok !== undefined) {
    try {
      const j = JSON.parse(res.stdout || "{}");
      if (!!j.ok !== expect.ok) return { ok: false };
    } catch { return { ok: false }; }
  }
  if (expect.jsonpath_eq) {
    try {
      const j = JSON.parse(res.stdout || "{}");
      const k = Object.keys(expect.jsonpath_eq)[0];
      const key = k.replace(/^\$\./, "");
      const want = expect.jsonpath_eq[k];
      if (JSON.stringify(j[key]) !== JSON.stringify(want)) return { ok: false };
    } catch { return { ok: false }; }
  }
  if (expect.nonempty) {
    try {
      const j = JSON.parse(res.stdout || "{}");
      if (Object.keys(j).length === 0) return { ok: false };
    } catch { return { ok: false }; }
  }
  return { ok: true };
}

function explainPlan(plan, targetPhase) {
  const selected = plan.phases.get(targetPhase);
  if (!selected) throw new Error(`unknown phase "${targetPhase}"`);
  const payload = {
    phase: selected.id,
    inherits: [...selected.inherits],
    rules: selected.rules.map((rule) => ({ ...rule }))
  };
  process.stdout.write(`${JSON.stringify(payload, null, 2)}\n`);
}

function usage() {
  console.log("usage: tf <validate|effects|graph|open|run|explain> ...");
  process.exit(2);
}

(async function main() {
  const [cmd, ...argv] = process.argv.slice(2);
  if (!cmd) usage();

  if (cmd === "validate") {
    const code = await runValidateCommand(argv);
    process.exit(code);
  }

  if (cmd === "effects") {
    const code = await runEffectsCommand(argv[0]);
    process.exit(code);
  }

  if (cmd === "graph") {
    const code = await runGraphCommand(argv);
    process.exit(code);
  }

  if (cmd === "open") {
    const [node] = argv;
    if (!node) { console.error("usage: tf open <NODE>"); process.exit(2); }
    const plan = loadRulebookPlan(rbPath(node));
    console.log("Node:", node);
    console.log("Phases:", [...plan.phases.keys()].join(", "));
    process.exit(0);
  }

  if (cmd === "explain") {
    const [rulebookArg, phaseId] = argv;
    if (!rulebookArg || !phaseId) {
      console.error("usage: tf explain <rulebook.yml|NODE> <PHASE>");
      process.exit(2);
    }
    const rulebookPath = resolveRulebookPath(rulebookArg);
    const plan = loadRulebookPlan(rulebookPath);
    explainPlan(plan, phaseId);
    process.exit(0);
  }

  if (cmd === "run") {
    const [node, cp, ...rest] = argv;
    if (!node || !cp) {
      console.error("usage: tf run <NODE> <CP> [--diff -] [--explain]");
      process.exit(2);
    }

    const diffIndex = rest.indexOf("--diff");
    let diff = "";
    if (diffIndex !== -1 && rest[diffIndex + 1] === "-") {
      diff = fs.readFileSync(0, "utf8");
    } else {
      try { diff = execSync("git diff -U0 --no-color", { encoding: "utf8" }); }
      catch { diff = ""; }
    }

    const diffPath = writeDiff(diff);
    const plan = loadRulebookPlan(rbPath(node));
    if (rest.includes("--explain")) explainPlan(plan, cp);
    const selected = rulesForPhaseFromPlan(plan, cp);
    const results = {};
    const evidence = [];

    for (const r of selected) {
      if (r.kind === "fs") {
        const missing = (r.files || []).filter((f) => !fs.existsSync(f));
        const ok = missing.length === 0;
        results[r.id] = { ok, reason: ok ? null : `missing:${missing.join(",")}` };
        evidence.push({ id: r.id, cmd: "fs", code: ok ? 0 : 1, out: JSON.stringify({ missing }) });
        if (!ok) console.error(`[FAIL] ${r.id} — missing ${missing.join(", ")}`);
        continue;
      }
      const command = r.cmd || r.command;
      if (!command) { results[r.id] = { ok: false, reason: "unsupported-kind" }; continue; }
      const res = run(command, { ...(r.env || {}), DIFF_PATH: diffPath });
      const ch = check(res, r.expect || {});
      results[r.id] = { ok: ch.ok, code: res.code, reason: ch.reason || null };
      evidence.push({ id: r.id, cmd: command, code: res.code, out: (res.stdout || "").slice(0, 2000) });
      if (!ch.ok) console.error(`[FAIL] ${r.id} — ${command}`);
    }

    const report = {
      contract_id: `${node}@0.45`,
      node_id: node,
      checkpoint: cp,
      timestamp: new Date().toISOString(),
      results,
      evidence
    };
    fs.mkdirSync("out", { recursive: true });
    fs.writeFileSync("out/TFREPORT.json", JSON.stringify(report, null, 2));
    const ok = Object.values(results).every((v) => v.ok);
    console.log(`\nRESULT: ${ok ? "GREEN" : "RED"}  (${Object.keys(results).length} probes)`);
    process.exit(ok ? 0 : 3);
  }

  usage();
})().catch((e) => {
  console.error(e?.message ?? e);
  process.exit(99);
});
