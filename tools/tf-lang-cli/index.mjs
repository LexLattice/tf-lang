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

// Track G (instances)
import annotateInstances, { normalizeChannel } from "../../packages/expander/resolve.mjs";

// Track F (typecheck)
import { typecheckFile, formatPortPath } from "../../packages/typechecker/typecheck.mjs";

// Track H (laws)
import { checkL0 } from "../../packages/checker/check.mjs";
import { findCounterexample } from "../../packages/prover/counterexample.mjs";

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

/* ----------------------- Track F: typecheck helpers ----------------------- */

function defaultAdapterRegistry() {
  return path.join(repoRoot, "adapters", "registry.json");
}

function portLabelOf(mismatch) {
  const portName =
    mismatch.port ??
    (Array.isArray(mismatch.portPath) ? formatPortPath(mismatch.portPath) : null);
  if (portName && portName !== "default") {
    return `${mismatch.nodeId}.${portName}`;
  }
  return `${mismatch.nodeId}`;
}

function formatMismatchLine(mismatch, describe) {
  const base = ` - ${portLabelOf(mismatch)}: ${mismatch.sourceVar} (${describe(
    mismatch.actual
  )}) → ${describe(mismatch.expected)}`;
  return mismatch.adapter
    ? `${base} via Transform(op: ${mismatch.adapter.op})`
    : base;
}

async function runTypecheckCommand(rawArgs) {
  const argv = Array.isArray(rawArgs) ? [...rawArgs] : rawArgs ? [rawArgs] : [];
  let registryPath = defaultAdapterRegistry();
  const files = [];

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--adapters") {
      const next = argv[i + 1];
      if (!next) {
        console.error("usage: tf typecheck <L0_FILE> [--adapters <registry.json>]");
        return 2;
      }
      registryPath = next;
      i += 1;
      continue;
    }
    const match = /^--adapters=(.+)$/u.exec(arg);
    if (match) {
      registryPath = match[1];
      continue;
    }
    files.push(arg);
  }

  if (files.length !== 1) {
    console.error("usage: tf typecheck <L0_FILE> [--adapters <registry.json>]");
    return 2;
  }

  const [file] = files;

  let report;
  try {
    report = await typecheckFile(file, { registryPath });
  } catch (error) {
    console.error(`${file}: ${error?.message ?? error}`);
    return 1;
  }

  const describe = typeof report.describe === "function" ? report.describe : () => "unknown";

  if (report.status === "ok" && report.mismatches.length === 0) {
    console.log("OK");
    return 0;
  }

  if (report.status === "needs-adapter") {
    const suggestions = report.suggestions ?? report.mismatches ?? [];
    const count = suggestions.length;
    console.log(`OK with ${count} suggestion(s)`);
    for (const mismatch of suggestions) {
      console.log(formatMismatchLine(mismatch, describe));
    }
    return 0;
  }

  const mismatches = report.mismatches ?? [];
  console.log(`FAILED with ${mismatches.length} mismatch(es)`);
  for (const mismatch of mismatches) {
    console.log(formatMismatchLine(mismatch, describe));
  }
  return 1;
}

/* -------------------------- Shared schema helpers ------------------------- */

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

/* ------------------------------ Effects / DOT ----------------------------- */

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
    if (arg === "--strict-graph") {
      strictGraph = true;
      continue;
    }
    if (arg === "--no-strict-graph") {
      strictGraph = false;
      continue;
    }
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

/* --------------------------- Rulebook / Checkpoint ------------------------ */

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
  return {
    code: r.status ?? 99,
    stdout: (r.stdout || "").trim(),
    stderr: (r.stderr || "").trim()
  };
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
    } catch {
      return { ok: false };
    }
  }
  if (expect.jsonpath_eq) {
    try {
      const j = JSON.parse(res.stdout || "{}");
      const k = Object.keys(expect.jsonpath_eq)[0];
      const key = k.replace(/^\$\./, "");
      const want = expect.jsonpath_eq[k];
      if (JSON.stringify(j[key]) !== JSON.stringify(want)) return { ok: false };
    } catch {
      return { ok: false };
    }
  }
  if (expect.nonempty) {
    try {
      const j = JSON.parse(res.stdout || "{}");
      if (Object.keys(j).length === 0) return { ok: false };
    } catch {
      return { ok: false };
    }
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

/* ------------------------ Track G: plan-instances CLI --------------------- */

function channelScheme(channel) {
  const value = normalizeChannel(channel);
  if (!value) return "none";
  if (value.startsWith("@")) return "dynamic";
  const [primary, remainder] = value.split(":", 2);
  if (primary === "rpc" && remainder) {
    const direction = remainder.split(":", 1)[0];
    return `${primary}:${direction}`;
  }
  return primary;
}

function cloneNodes(input) {
  return Array.isArray(input) ? JSON.parse(JSON.stringify(input)) : [];
}

function collectNodes(doc) {
  const nodes = [];
  nodes.push(...cloneNodes(doc?.nodes));
  if (Array.isArray(doc?.monitors)) {
    for (const monitor of doc.monitors) {
      nodes.push(...cloneNodes(monitor?.nodes));
    }
  }
  return nodes;
}

function sortObject(obj, mapFn = (value) => value) {
  return Object.fromEntries(
    Object.keys(obj)
      .sort()
      .map((key) => [key, mapFn(obj[key])])
  );
}

function finalizeDomainSummary(domains) {
  return sortObject(domains, (value) => ({
    total: value.total,
    instances: sortObject(value.instances)
  }));
}

function finalizeSchemeSummary(schemes) {
  return sortObject(schemes, (value) => ({
    total: value.total,
    instances: sortObject(value.instances)
  }));
}

async function runPlanInstancesCommand(rawArgs) {
  const argv = Array.isArray(rawArgs) ? [...rawArgs] : rawArgs != null ? [rawArgs] : [];
  let registryPath;
  let groupBy = "domain";
  const files = [];

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--registry") {
      const value = argv[i + 1];
      if (value === undefined || value.startsWith("--")) {
        console.error("Error: --registry requires a value.");
        return 2;
      }
      registryPath = value;
      i += 1;
      continue;
    }
    if (arg?.startsWith("--registry=")) {
      registryPath = arg.split("=", 2)[1];
      continue;
    }
    if (arg === "--group-by") {
      const value = argv[i + 1];
      if (value === undefined || value.startsWith("--")) {
        console.error("Error: --group-by requires a value.");
        return 2;
      }
      groupBy = value;
      i += 1;
      continue;
    }
    if (arg?.startsWith("--group-by=")) {
      groupBy = arg.split("=", 2)[1];
      continue;
    }
    files.push(arg);
  }

  if (files.length !== 1) {
    console.error("usage: tf plan-instances [--registry <path>] [--group-by domain|scheme] <FILE>");
    return 2;
  }

  if (!["domain", "scheme"].includes(groupBy)) {
    console.error("--group-by must be one of: domain, scheme");
    return 2;
  }

  const [file] = files;

  try {
    const doc = await loadJsonFile(file);
    const nodes = collectNodes(doc);
    const registry = registryPath ? JSON.parse(await readFile(registryPath, "utf8")) : undefined;
    annotateInstances({ nodes, registry });

    const domains = {};
    const schemes = {};

    for (const node of nodes) {
      const domain = node.runtime?.domain ?? "default";
      const instance = node.runtime?.instance ?? "@Memory";
      const scheme = channelScheme(node.channel);

      if (!domains[domain]) {
        domains[domain] = { total: 0, instances: {} };
      }
      domains[domain].total += 1;
      domains[domain].instances[instance] = (domains[domain].instances[instance] || 0) + 1;

      if (!schemes[scheme]) {
        schemes[scheme] = { total: 0, instances: {} };
      }
      schemes[scheme].total += 1;
      schemes[scheme].instances[instance] = (schemes[scheme].instances[instance] || 0) + 1;
    }

    const summary =
      groupBy === "domain"
        ? { domains: finalizeDomainSummary(domains), channels: finalizeSchemeSummary(schemes) }
        : { schemes: finalizeSchemeSummary(schemes), domains: finalizeDomainSummary(domains) };

    console.log(JSON.stringify(summary, null, 2));
    return 0;
  } catch (err) {
    console.error(`${file}: ${err?.message ?? err}`);
    return 1;
  }
}

/* --------------------------- Track H: laws CLI ---------------------------- */

function summarizeLawStatus(report) {
  if (!report) return "NEUTRAL";
  const entries = Array.isArray(report.results) ? report.results : [];
  if (entries.some((entry) => entry.status === "ERROR")) return "RED";
  if (entries.some((entry) => entry.status === "WARN")) return "WARN";
  if (entries.some((entry) => entry.status === "PASS")) return "PASS";
  if (entries.length === 0) return report.ok === false ? "RED" : "NEUTRAL";
  return entries[0]?.status ?? "NEUTRAL";
}

function printBranchEntry(entry) {
  const label = entry.branch || entry.guardVar || "(branch)";
  const parts = [`  - ${label}: ${entry.status}`];
  if (entry.guard) parts.push(`guard=${entry.guard}`);
  if (entry.proved === true) parts.push("proved=true");
  else if (entry.proved === false) parts.push("proved=false");
  if (entry.reason) parts.push(`reason=${entry.reason}`);
  console.log(parts.join(" "));
}

function printMonotonicEntry(entry) {
  const parts = [`  - ${entry.id ?? "(node)"}: ${entry.status}`];
  if (entry.assumption) parts.push(`assumption=${entry.assumption}`);
  if (entry.reason) parts.push(`reason=${entry.reason}`);
  console.log(parts.join(" "));
}

function printConfidentialEntry(entry) {
  const parts = [`  - ${entry.id ?? "(node)"}: ${entry.status}`];
  if (entry.reason) parts.push(`reason=${entry.reason}`);
  if (entry.satisfied === true) parts.push("satisfied=true");
  else if (entry.satisfied === false) parts.push("satisfied=false");
  console.log(parts.join(" "));
}

function formatAssignment(assignment) {
  if (!assignment || typeof assignment !== "object") {
    return "(none)";
  }
  const keys = Object.keys(assignment).sort();
  if (keys.length === 0) {
    return "(empty)";
  }
  return keys.map((key) => `${key}=${assignment[key] ? "true" : "false"}`).join(", ");
}

function collectBranchVariables(entry) {
  const variables = new Set();
  const add = (items = []) => {
    for (const item of items) {
      const name = item?.guard?.var;
      if (typeof name === "string") {
        variables.add(name);
      }
    }
  };
  add(entry?.positive);
  add(entry?.negative);
  return Array.from(variables).sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}

function sortBranchResults(entries = []) {
  return [...entries].sort((a, b) => {
    const aKey = a.branch ?? a.guardVar ?? "";
    const bKey = b.branch ?? b.guardVar ?? "";
    if (aKey < bKey) return -1;
    if (aKey > bKey) return 1;
    return 0;
  });
}

function sortNodeResults(entries = []) {
  return [...entries].sort((a, b) => {
    const aId = a.id ?? "";
    const bId = b.id ?? "";
    if (aId < bId) return -1;
    if (aId > bId) return 1;
    const aChannel = a.channel ?? "";
    const bChannel = b.channel ?? "";
    if (aChannel < bChannel) return -1;
    if (aChannel > bChannel) return 1;
    return 0;
  });
}

function consumeFlagWithValue(argv, i, long) {
  const arg = argv[i];
  if (arg === `--${long}`) {
    const value = argv[i + 1];
    if (value === undefined) {
      console.error(`missing value for --${long}`);
      return { i, err: 2 };
    }
    return { i: i + 1, value };
  }
  if (typeof arg === "string" && arg.startsWith(`--${long}=`)) {
    return { i, value: arg.slice(long.length + 3) };
  }
  return null;
}

function evaluateGuard(guard, assignment) {
  if (!guard || guard.kind !== "var" || typeof guard.var !== "string") {
    return false;
  }
  const value = Boolean(assignment[guard.var]);
  return guard.negated ? !value : value;
}

function evaluateBranchEntry(entry, assignment) {
  const positives = Array.isArray(entry?.positive) ? entry.positive : [];
  const negatives = Array.isArray(entry?.negative) ? entry.negative : [];
  const positiveActive = positives.some((item) => evaluateGuard(item.guard, assignment));
  const negativeActive = negatives.some((item) => evaluateGuard(item.guard, assignment));
  return !(positiveActive && negativeActive);
}

async function runLawsCommand(rawArgs) {
  const argv = Array.isArray(rawArgs) ? [...rawArgs] : [];
  if (argv[0] !== "--check" || !argv[1]) {
    console.error(
      "usage: tf laws --check <L0_FILE> [--goal branch-exclusive] [--max-bools N] [--json] [--policy <path>] [--caps <path>]"
    );
    return 2;
  }

  const file = argv[1];
  let goal = null;
  let maxBools = 8;
  let jsonMode = false;
  let policyPath;
  let capsPath;

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    if (!arg) continue;

    const goalHit = consumeFlagWithValue(argv, i, "goal");
    if (goalHit) {
      if (goalHit.err) return goalHit.err;
      goal = goalHit.value;
      i = goalHit.i;
      continue;
    }

    const maxBoolsHit = consumeFlagWithValue(argv, i, "max-bools");
    if (maxBoolsHit) {
      if (maxBoolsHit.err) return maxBoolsHit.err;
      maxBools = Number(maxBoolsHit.value);
      i = maxBoolsHit.i;
      continue;
    }

    if (arg === "--json") {
      jsonMode = true;
      continue;
    }

    const policyHit = consumeFlagWithValue(argv, i, "policy");
    if (policyHit) {
      if (policyHit.err) return policyHit.err;
      policyPath = policyHit.value;
      i = policyHit.i;
      continue;
    }

    const capsHit = consumeFlagWithValue(argv, i, "caps");
    if (capsHit) {
      if (capsHit.err) return capsHit.err;
      capsPath = capsHit.value;
      i = capsHit.i;
      continue;
    }

    console.error(`unknown option: ${arg}`);
    return 2;
  }

  if (goal && goal !== "branch-exclusive") {
    console.error(`unknown goal: ${goal}`);
    return 2;
  }
  if (!Number.isInteger(maxBools) || Number.isNaN(maxBools) || maxBools < 1) {
    console.error("invalid --max-bools value");
    return 2;
  }

  try {
    const options = {};
    if (policyPath) options.policyPath = policyPath;
    if (capsPath) options.capsPath = capsPath;

    const report = await checkL0(file, options);
    const lawReports = report?.laws ?? {};
    const order = ["branch_exclusive", "monotonic_log", "confidential_envelope"];
    const normalized = {};
    let overallGreen = true;

    for (const name of order) {
      const source = lawReports[name];
      const snapshot = source ? { ...source } : { ok: true, results: [] };
      snapshot.results = Array.isArray(snapshot.results) ? snapshot.results : [];
      const errorEntry = snapshot.results.some((entry) => entry?.status === "ERROR");
      if (snapshot.ok === undefined) snapshot.ok = !errorEntry;
      if (snapshot.ok === false || errorEntry) overallGreen = false;
      normalized[name] = snapshot;
    }

    const status = overallGreen ? "GREEN" : "RED";

    let counterexample = null;
    if (!overallGreen && goal === "branch-exclusive") {
      const branchReport = normalized.branch_exclusive;
      const failing = branchReport?.results?.find((entry) => entry.status === "ERROR");
      if (failing) {
        const variables = collectBranchVariables(failing);
        try {
          counterexample = findCounterexample({
            goal: "branch-exclusive",
            guard: failing.guard ?? null,
            reason: failing.reason ?? "overlap",
            variables,
            positive: failing.positive,
            negative: failing.negative,
            predicate: (candidate) => evaluateBranchEntry(failing, candidate),
            maxBools
          });
        } catch (error) {
          if (!jsonMode) {
            console.error(`counterexample search failed: ${error?.message ?? error}`);
          }
          return 1;
        }
      }
    }

    if (jsonMode) {
      const output = {
        status,
        laws: {}
      };
      for (const name of order) output.laws[name] = normalized[name];
      if (status === "RED" && goal === "branch-exclusive" && counterexample) {
        output.counterexample = counterexample;
      }
      console.log(JSON.stringify(output, null, 2));
    } else {
      console.log(`Laws for ${file}:`);
      console.log(`status: ${status}`);
      for (const name of order) {
        const law = normalized[name];
        const summary = summarizeLawStatus(law);
        console.log(`${name}: ${summary}`);
        const entries = Array.isArray(law.results) ? law.results : [];
        if (entries.length === 0) {
          console.log("  (no matches)");
          continue;
        }
        let sorted = entries;
        if (name === "branch_exclusive") sorted = sortBranchResults(entries);
        else sorted = sortNodeResults(entries);

        for (const entry of sorted) {
          if (name === "branch_exclusive") printBranchEntry(entry);
          else if (name === "monotonic_log") printMonotonicEntry(entry);
          else if (name === "confidential_envelope") printConfidentialEntry(entry);
          else console.log(`  - ${JSON.stringify(entry)}`);
        }
      }

      if (status === "RED" && goal === "branch-exclusive") {
        if (counterexample) {
          const guardText = counterexample.guard ? ` guard=${counterexample.guard}` : "";
          console.log(
            `Counterexample: ${formatAssignment(counterexample.assignment)} reason=${counterexample.reason}${guardText}`
          );
          const triggered = counterexample.triggered ?? {};
          const positive =
            Array.isArray(triggered.positive) && triggered.positive.length > 0
              ? triggered.positive.join(", ")
              : "(none)";
          const negative =
            Array.isArray(triggered.negative) && triggered.negative.length > 0
              ? triggered.negative.join(", ")
              : "(none)";
          console.log(`  positive: ${positive}`);
          console.log(`  negative: ${negative}`);
        } else {
          console.log("Counterexample: none found within bounds");
        }
      }
    }

    return overallGreen ? 0 : 1;
  } catch (error) {
    console.error(error?.message ?? error);
    return 1;
  }
}

/* --------------------------------- Usage ---------------------------------- */

function usage() {
  console.log(
    "usage: tf <validate|effects|graph|typecheck|plan-instances|laws|open|run|explain> ..."
  );
  console.log("       tf validate [l0|l2] <FILE...>");
  console.log("       tf effects <FILE>");
  console.log("       tf graph [--strict-graph[=true|false]] <FILE>");
  console.log("       tf typecheck <L0_FILE> [--adapters <registry.json>]");
  console.log("       tf plan-instances [--registry <path>] [--group-by domain|scheme] <FILE>");
  console.log(
    "       tf laws --check <L0_FILE> [--goal branch-exclusive] [--max-bools N] [--json] [--policy <path>] [--caps <path>]"
  );
  process.exit(2);
}

/* --------------------------------- Main ----------------------------------- */

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

  if (cmd === "typecheck") {
    const code = await runTypecheckCommand(argv);
    process.exit(code);
  }

  if (cmd === "plan-instances") {
    const code = await runPlanInstancesCommand(argv);
    process.exit(code);
  }

  if (cmd === "laws") {
    const code = await runLawsCommand(argv);
    process.exit(code);
  }

  if (cmd === "open") {
    const [node] = argv;
    if (!node) {
      console.error("usage: tf open <NODE>");
      process.exit(2);
    }
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
      try {
        diff = execSync("git diff -U0 --no-color", { encoding: "utf8" });
      } catch {
        diff = "";
      }
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
        evidence.push({
          id: r.id,
          cmd: "fs",
          code: ok ? 0 : 1,
          out: JSON.stringify({ missing })
        });
        if (!ok) console.error(`[FAIL] ${r.id} — missing ${missing.join(", ")}`);
        continue;
      }
      const command = r.cmd || r.command;
      if (!command) {
        results[r.id] = { ok: false, reason: "unsupported-kind" };
        continue;
      }
      const res = run(command, { ...(r.env || {}), DIFF_PATH: diffPath });
      const ch = check(res, r.expect || {});
      results[r.id] = { ok: ch.ok, code: res.code, reason: ch.reason || null };
      evidence.push({
        id: r.id,
        cmd: command,
        code: res.code,
        out: (res.stdout || "").slice(0, 2000)
      });
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
