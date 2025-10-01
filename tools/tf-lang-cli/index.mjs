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
import annotateInstances, { normalizeChannel, explainInstanceSelection } from "../../packages/expander/resolve.mjs";
import { expandPipelineFromFile } from "../../packages/expander/expand.mjs";

// Track F (typecheck)
import { typecheckFile, formatPortPath } from "../../packages/typechecker/typecheck.mjs";

// Track H (laws)
import { checkL0 } from "../../packages/checker/check.mjs";
import { findCounterexample } from "../../packages/prover/counterexample.mjs";
import { LAW_GOALS, LAW_GOALS_BY_ID, LAW_GOALS_BY_KEY } from "../../packages/checker/law-goals.mjs";
import executeL0 from "../../packages/runtime/run.mjs";
import { registerTransform, getTransform } from "../../packages/transform/index.mjs";

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
  let emitDir = null;
  const files = [];

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    const adaptersHit = consumeFlagWithValue(argv, i, "adapters");
    if (adaptersHit) {
      if (adaptersHit.err) return adaptersHit.err;
      registryPath = adaptersHit.value;
      i = adaptersHit.i;
      continue;
    }
    if (arg === "--emit-adapters") {
      const next = argv[i + 1];
      if (!next || next.startsWith("--")) {
        console.error("usage: tf typecheck <L0_FILE> [--adapters <registry.json>] [--emit-adapters <dir>]");
        return 2;
      }
      emitDir = next;
      i += 1;
      continue;
    }
    if (arg?.startsWith("--emit-adapters=")) {
      emitDir = arg.split("=", 2)[1];
      continue;
    }
    files.push(arg);
  }

  if (files.length !== 1) {
    console.error("usage: tf typecheck <L0_FILE> [--adapters <registry.json>] [--emit-adapters <dir>]");
    return 2;
  }

  const [file] = files;

  let report;
  try {
    const options = { registryPath };
    if (emitDir) options.emitAdaptersDir = emitDir;
    report = await typecheckFile(file, options);
  } catch (error) {
    console.error(`${file}: ${error?.message ?? error}`);
    return 1;
  }

  const describe = typeof report.describe === "function" ? report.describe : () => "unknown";

  if (report.status === "ok" && report.mismatches.length === 0) {
    console.log("OK");
    if (report.emittedAdapters?.length) {
      console.log(`Emitted ${report.emittedAdapters.length} adapter stub(s) to ${emitDir}`);
      for (const entry of report.emittedAdapters) {
        console.log(` - ${entry.op} → ${entry.file}`);
      }
    }
    return 0;
  }

  if (report.status === "needs-adapter") {
    const suggestions = report.suggestions ?? report.mismatches ?? [];
    const count = suggestions.length;
    console.log(`OK with ${count} suggestion(s)`);
    for (const mismatch of suggestions) {
      console.log(formatMismatchLine(mismatch, describe));
    }
    if (report.emittedAdapters?.length) {
      console.log(`Emitted ${report.emittedAdapters.length} adapter stub(s) to ${emitDir}`);
      for (const entry of report.emittedAdapters) {
        console.log(` - ${entry.op} → ${entry.file}`);
      }
    }
    return 0;
  }

  const mismatches = report.mismatches ?? [];
  console.log(`FAILED with ${mismatches.length} mismatch(es)`);
  for (const mismatch of mismatches) {
    console.log(formatMismatchLine(mismatch, describe));
  }
  if (report.emittedAdapters?.length) {
    console.log(`Emitted ${report.emittedAdapters.length} adapter stub(s) to ${emitDir}`);
    for (const entry of report.emittedAdapters) {
      console.log(` - ${entry.op} → ${entry.file}`);
    }
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

function buildPlanSummary(nodes) {
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

  return {
    domains: finalizeDomainSummary(domains),
    schemes: finalizeSchemeSummary(schemes)
  };
}

function summarizeGroupForTable(entries) {
  const rows = [];
  for (const [groupName, entry] of Object.entries(entries)) {
    const instanceEntries = Object.entries(entry.instances);
    instanceEntries.sort(([a], [b]) => a.localeCompare(b));
    rows.push({ group: groupName, instance: "TOTAL", count: entry.total, isTotal: true });
    for (const [instance, count] of instanceEntries) {
      rows.push({ group: groupName, instance, count, isTotal: false });
    }
  }
  return rows;
}

function formatGroupTable(title, groupLabel, entries) {
  const rows = summarizeGroupForTable(entries);
  if (rows.length === 0) {
    return `${title}\n( no entries )`;
  }
  const groupWidth = Math.max(groupLabel.length, ...rows.map((row) => row.group.length));
  const instanceWidth = Math.max("Instance".length, ...rows.map((row) => row.instance.length));
  const countWidth = Math.max("Count".length, ...rows.map((row) => String(row.count).length));

  const lines = [];
  lines.push(title);
  lines.push(
    `${groupLabel.padEnd(groupWidth)}  ${"Instance".padEnd(instanceWidth)}  ${"Count".padStart(countWidth)}`
  );
  lines.push(
    `${"-".repeat(groupWidth)}  ${"-".repeat(instanceWidth)}  ${"-".repeat(countWidth)}`
  );

  for (const row of rows) {
    const displayGroup = row.isTotal ? row.group : "";
    const groupCell = displayGroup.padEnd(groupWidth);
    const instanceCell = row.instance.padEnd(instanceWidth);
    const countCell = String(row.count).padStart(countWidth);
    lines.push(`${groupCell}  ${instanceCell}  ${countCell}`);
  }

  return lines.join("\n");
}

function describeWhenClause(when = {}) {
  const parts = [];
  if ("domain" in when) parts.push(`domain=${JSON.stringify(when.domain)}`);
  if ("channel" in when) parts.push(`channel=${JSON.stringify(when.channel)}`);
  if ("qos" in when) parts.push(`qos=${JSON.stringify(when.qos)}`);
  return parts.join(", ");
}

function buildPlanDetails(nodes, registry) {
  const details = [];
  for (const node of nodes) {
    const runtime = node.runtime || {};
    const selection = explainInstanceSelection(node, {
      registry,
      domain: runtime.domain
    });
    details.push({
      id: node.id,
      kind: node.kind,
      domain: runtime.domain ?? selection.context?.domain ?? "default",
      scheme: channelScheme(node.channel),
      instance: runtime.instance ?? selection.instance,
      hint: runtime.hint ?? null,
      resolved: selection.instance,
      source: selection.source,
      ruleIndex: selection.ruleIndex,
      rule: selection.rule || null
    });
  }
  details.sort((a, b) => a.id.localeCompare(b.id));
  return details;
}

function formatPlanDetails(details) {
  if (!details.length) {
    return "Details:\n( no kernel nodes )";
  }
  const lines = ["Details:"];
  for (const detail of details) {
    lines.push(
      `- ${detail.id} (${detail.kind}) → ${detail.instance} [domain=${detail.domain}, scheme=${detail.scheme}]`
    );
    let sourceLine = "  source: ";
    if (detail.source === "rule") {
      const clause = describeWhenClause(detail.rule?.when ?? {});
      const suffix = clause ? ` (${clause})` : "";
      sourceLine += `registry rule ${detail.ruleIndex + 1}${suffix}`;
    } else if (detail.source === "domain") {
      sourceLine += "registry domain override";
    } else {
      sourceLine += "registry default";
    }
    lines.push(sourceLine);
    if (detail.hint) {
      const matches = detail.hint === detail.instance;
      const note = matches ? "matches selection" : `differs → resolved ${detail.resolved}`;
      lines.push(`  hint: ${detail.hint} (${note})`);
    }
  }
  return lines.join("\n");
}

async function runPlanInstancesCommand(rawArgs) {
  const argv = Array.isArray(rawArgs) ? [...rawArgs] : rawArgs != null ? [rawArgs] : [];
  let registryPath;
  let groupBy = "domain";
  let format = "json";
  let explain = false;
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
    if (arg === "--format") {
      const value = argv[i + 1];
      if (value === undefined || value.startsWith("--")) {
        console.error("Error: --format requires a value.");
        return 2;
      }
      format = value;
      i += 1;
      continue;
    }
    if (arg?.startsWith("--format=")) {
      format = arg.split("=", 2)[1];
      continue;
    }
    if (arg === "--explain") {
      explain = true;
      continue;
    }
    files.push(arg);
  }

  if (files.length !== 1) {
    console.error(
      "usage: tf plan-instances [--registry <path>] [--group-by domain|scheme] [--format json|table] [--explain] <FILE>"
    );
    return 2;
  }

  if (!["domain", "scheme"].includes(groupBy)) {
    console.error("--group-by must be one of: domain, scheme");
    return 2;
  }

  if (!["json", "table"].includes(format)) {
    console.error("--format must be one of: json, table");
    return 2;
  }

  const [file] = files;

  try {
    const doc = await loadJsonFile(file);
    const nodes = collectNodes(doc);
    const registry = registryPath ? JSON.parse(await readFile(registryPath, "utf8")) : undefined;
    annotateInstances({ nodes, registry });

    const summary = buildPlanSummary(nodes);
    const payload =
      groupBy === "domain"
        ? { domains: summary.domains, schemes: summary.schemes }
        : { schemes: summary.schemes, domains: summary.domains };

    if (groupBy === "domain") {
      payload.channels = summary.schemes;
    }

    if (format === "json") {
      if (explain) {
        payload.details = buildPlanDetails(nodes, registry);
      }
      payload.groupBy = groupBy;
      console.log(JSON.stringify(payload, null, 2));
    } else {
      const primaryLabel = groupBy === "domain" ? "Domain" : "Scheme";
      const primarySummary = groupBy === "domain" ? summary.domains : summary.schemes;
      const secondaryLabel = groupBy === "domain" ? "Scheme" : "Domain";
      const secondarySummary = groupBy === "domain" ? summary.schemes : summary.domains;

      console.log(formatGroupTable(`${primaryLabel} → Instance plan`, primaryLabel, primarySummary));
      console.log("");
      console.log(formatGroupTable(`${secondaryLabel} coverage`, secondaryLabel, secondarySummary));

      if (explain) {
        console.log("");
        console.log(formatPlanDetails(buildPlanDetails(nodes, registry)));
      }
    }
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

function displayPath(p) {
  if (!p || typeof p !== "string") return null;
  const relative = path.relative(process.cwd(), p);
  if (!relative || relative.startsWith("..")) return p;
  return relative;
}

function formatSummaryRow(label, status, details) {
  const labelWidth = 22;
  const statusWidth = 8;
  const safeLabel = String(label ?? "");
  const safeStatus = String(status ?? "N/A");
  const safeDetails = details ? String(details) : "";
  return `${safeLabel.padEnd(labelWidth)} ${safeStatus.padEnd(statusWidth)} ${safeDetails}`.trimEnd();
}

function describeEffectsSummary(effects) {
  if (!effects || typeof effects !== "object") return "no data";
  const parts = [];
  if (effects.declared) parts.push(`declared=${effects.declared}`);
  if (effects.computed && effects.computed !== effects.declared) {
    parts.push(`computed=${effects.computed}`);
  }
  const missing = Array.isArray(effects.missing) ? effects.missing.length : 0;
  if (missing > 0) parts.push(`missing=${missing}`);
  const extra = Array.isArray(effects.extra) ? effects.extra.length : 0;
  if (extra > 0) parts.push(`extra=${extra}`);
  if (parts.length === 0) parts.push("matched");
  return parts.join(" ");
}

function describePolicySummary(policy) {
  if (!policy || typeof policy !== "object") return "no data";
  const violations = Array.isArray(policy.violations) ? policy.violations.length : 0;
  const dynamic = Array.isArray(policy.dynamic) ? policy.dynamic.length : 0;
  const parts = [`violations=${violations}`];
  if (dynamic > 0) parts.push(`dynamic=${dynamic}`);
  return parts.join(" ");
}

function describeCapabilitiesSummary(caps) {
  if (!caps || typeof caps !== "object") return "no data";
  const required = Array.isArray(caps.required) ? caps.required.length : 0;
  const missing = Array.isArray(caps.missing) ? caps.missing.length : 0;
  const parts = [`required=${required}`];
  if (missing > 0) parts.push(`missing=${missing}`);
  if (Array.isArray(caps.extras) && caps.extras.length > 0) {
    parts.push(`extras=${caps.extras.length}`);
  }
  return parts.join(" ");
}

function lawEntryStatus(entry) {
  const status = summarizeLawStatus(entry);
  return status ?? "NEUTRAL";
}

function describeLawSummary(entry) {
  if (!entry || typeof entry !== "object") return "no data";
  const results = Array.isArray(entry.results) ? entry.results : [];
  const flagged = results.filter((item) => {
    if (item?.ok === false) return true;
    if (typeof item?.status === "string") {
      const normalized = item.status.toUpperCase();
      return !["PASS", "OK", "GREEN", "SAT"].includes(normalized);
    }
    return false;
  }).length;
  const parts = [`${results.length} result(s)`];
  if (flagged > 0) parts.push(`${flagged} flagged`);
  const evidencePath = displayPath(entry?.evidence?.path);
  if (evidencePath) parts.push(`evidence=${evidencePath}`);
  return parts.join(", ");
}

function formatCheckSummary(report, { file } = {}) {
  if (!report || typeof report !== "object") return "No report";
  const lines = [];
  const location = displayPath(file);
  const pipelineId = report.pipeline_id ?? "unknown";
  const overallStatus = report.status ?? "UNKNOWN";
  lines.push(`Check summary${location ? ` for ${location}` : ""}`);
  lines.push(`Pipeline: ${pipelineId}`);
  lines.push(`Overall: ${overallStatus}`);
  lines.push("");

  const effectsStatus = report.effects?.ok === false ? "RED" : report.effects?.ok === true ? "GREEN" : "NEUTRAL";
  lines.push(formatSummaryRow("Effects", effectsStatus, describeEffectsSummary(report.effects)));

  const publish = report.policy?.publish ?? null;
  const publishStatus = publish?.ok === false ? "RED" : publish?.ok === true ? "GREEN" : "NEUTRAL";
  lines.push(formatSummaryRow("Policy publish", publishStatus, describePolicySummary(publish)));

  const subscribe = report.policy?.subscribe ?? null;
  const subscribeStatus = subscribe?.ok === false ? "RED" : subscribe?.ok === true ? "GREEN" : "NEUTRAL";
  lines.push(formatSummaryRow("Policy subscribe", subscribeStatus, describePolicySummary(subscribe)));

  const caps = report.capabilities ?? null;
  let capsStatus = "NEUTRAL";
  if (caps?.ok === false || (Array.isArray(caps?.missing) && caps.missing.length > 0)) capsStatus = "RED";
  else if (caps?.ok === true) capsStatus = "GREEN";
  lines.push(formatSummaryRow("Capabilities", capsStatus, describeCapabilitiesSummary(caps)));

  lines.push("");
  lines.push("Laws:");
  const lawEntries = Object.entries(report.laws ?? {});
  if (lawEntries.length === 0) {
    lines.push("  (none)");
  } else {
    for (const [key, entry] of lawEntries.sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))) {
      const label = entry?.name ?? key;
      const status = lawEntryStatus(entry);
      lines.push(formatSummaryRow(`  ${label}`, status, describeLawSummary(entry)));
    }
  }

  return lines.join("\n");
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
  if (Array.isArray(entry.issues) && entry.issues.length > 0) {
    parts.push(`issues=${entry.issues.join('|')}`);
  }
  if (entry.indexSource) parts.push(`index=${entry.indexSource}`);
  console.log(parts.join(" "));
}

function printConfidentialEntry(entry) {
  const parts = [`  - ${entry.id ?? "(node)"}: ${entry.status}`];
  if (entry.reason) parts.push(`reason=${entry.reason}`);
  if (entry.satisfied === true) parts.push("satisfied=true");
  else if (entry.satisfied === false) parts.push("satisfied=false");
  if (Array.isArray(entry.plaintextPaths) && entry.plaintextPaths.length > 0) {
    parts.push(`plaintext=${entry.plaintextPaths.join('|')}`);
  }
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

function goalMetadataForInput(value) {
  if (!value) return null;
  return LAW_GOALS_BY_ID.get(value) ?? LAW_GOALS_BY_KEY.get(value);
}

function printLawGoals() {
  console.log("Available law goals:");
  for (const goal of LAW_GOALS) {
    console.log(` - ${goal.id.padEnd(20)} ${goal.description}`);
  }
}

function consumeFlagWithValue(argv, i, long) {
  const arg = argv[i];
  if (arg === `--${long}`) {
    const value = argv[i + 1];
    if (value === undefined || value.startsWith('--')) {
      console.error(`missing value for --${long}`);
      return { i, err: 2 };
    }
    return { i: i + 1, value };
  }
  if (typeof arg === "string" && arg.startsWith(`--${long}=`)) {
    const raw = arg.slice(long.length + 3);
    if (!raw || raw.startsWith("--")) {
      console.error(`missing value for --${long}`);
      return { i, err: 2 };
    }
    return { i, value: raw };
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
  if (argv.length === 0) {
    console.error(
      "usage: tf laws --check <L0_FILE> [--goal <id>] [--verbose] [--max-bools N] [--json] [--policy <path>] [--caps <path>]"
    );
    console.error("       tf laws --list-goals");
    return 2;
  }

  if (argv[0] === "--list-goals") {
    printLawGoals();
    return 0;
  }

  if (argv[0] !== "--check" || !argv[1]) {
    console.error(
      "usage: tf laws --check <L0_FILE> [--goal <id>] [--verbose] [--max-bools N] [--json] [--policy <path>] [--caps <path>]"
    );
    console.error("       tf laws --list-goals");
    return 2;
  }

  const file = argv[1];
  let goalId = null;
  let maxBools = 8;
  let jsonMode = false;
  let policyPath;
  let capsPath;
  let verbose = false;

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    if (!arg) continue;

    const goalHit = consumeFlagWithValue(argv, i, "goal");
    if (goalHit) {
      if (goalHit.err) return goalHit.err;
      const meta = goalMetadataForInput(goalHit.value);
      if (!meta) {
        console.error(`unknown goal: ${goalHit.value}`);
        return 2;
      }
      goalId = meta.id;
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

    if (arg === "--verbose") {
      verbose = true;
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
    const lawsList = [];

    for (const goal of LAW_GOALS) {
      const source = lawReports[goal.key];
      const snapshot = source ? { ...source } : { ok: true, results: [] };
      const results = Array.isArray(snapshot.results) ? [...snapshot.results] : [];
      const goalOk = results.every((entry) => entry && entry.ok !== false && entry.status !== "ERROR");
      snapshot.results = results;
      if (!snapshot.goal) snapshot.goal = goal.id;
      if (!snapshot.name) snapshot.name = goal.name;
      if (!snapshot.key) snapshot.key = goal.key;
      if (snapshot.ok === undefined) {
        snapshot.ok = goalOk;
      } else if (snapshot.ok !== false) {
        snapshot.ok = goalOk;
      }
      lawsList.push({ meta: goal, report: snapshot });
    }

    for (const [rawKey, source] of Object.entries(lawReports)) {
      if (LAW_GOALS_BY_KEY.has(rawKey)) continue;
      const snapshot = source ? { ...source } : { ok: true, results: [] };
      const results = Array.isArray(snapshot.results) ? [...snapshot.results] : [];
      const goalOk = results.every((entry) => entry && entry.ok !== false && entry.status !== "ERROR");
      snapshot.results = results;
      if (snapshot.ok === undefined) {
        snapshot.ok = goalOk;
      } else if (snapshot.ok !== false) {
        snapshot.ok = goalOk;
      }
      const meta = { id: rawKey, key: rawKey, name: rawKey, description: rawKey };
      if (!snapshot.goal) snapshot.goal = meta.id;
      if (!snapshot.name) snapshot.name = meta.name;
      if (!snapshot.key) snapshot.key = meta.key;
      lawsList.push({ meta, report: snapshot });
    }

    const overallGreen = lawsList.every((entry) => {
      const reportEntry = entry?.report ?? {};
      const results = Array.isArray(reportEntry.results) ? reportEntry.results : [];
      const goalOk = results.every((item) => item && item.ok !== false && item.status !== "ERROR");
      if (reportEntry.ok === false) return false;
      return goalOk;
    });

    const status = overallGreen ? "GREEN" : "RED";

    let counterexample = null;
    if (!overallGreen && goalId === 'branch-exclusive') {
      const branchEntry = lawsList.find((entry) => entry.meta.id === 'branch-exclusive');
      const branchReport = branchEntry?.report;
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
      for (const entry of lawsList) {
        output.laws[entry.meta.key] = entry.report;
      }
      if (status === "RED" && goalId === 'branch-exclusive' && counterexample) {
        output.counterexample = counterexample;
      }
      console.log(JSON.stringify(output, null, 2));
    } else {
      console.log(`Laws for ${file}:`);
      console.log(`status: ${status}`);
      for (const entry of lawsList) {
        const { meta, report: law } = entry;
        const summary = summarizeLawStatus(law);
        const label = meta.id;
        console.log(`${label}: ${summary}`);
        if (verbose && law.evidence?.path) {
          console.log(`  evidence: ${law.evidence.path}`);
        }
        const entries = Array.isArray(law.results) ? law.results : [];
        if (entries.length === 0) {
          console.log("  (no matches)");
          continue;
        }
        let sorted = entries;
        if (meta.key === "branch_exclusive") sorted = sortBranchResults(entries);
        else sorted = sortNodeResults(entries);

        for (const entry of sorted) {
          if (meta.key === "branch_exclusive") printBranchEntry(entry);
          else if (meta.key === "monotonic_log") printMonotonicEntry(entry);
          else if (meta.key === "confidential_envelope") printConfidentialEntry(entry);
          else console.log(`  - ${JSON.stringify(entry)}`);
        }
      }

      if (status === "RED" && goalId === 'branch-exclusive') {
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

function runExpandCommand(argv) {
  if (argv.length === 0) {
    console.error("usage: tf expand <PIPELINE.l2.yaml> --out <PIPELINE.l0.json>");
    return 2;
  }
  const [input, ...rest] = argv;
  let outPath = null;
  let createdAt = null;
  for (let i = 0; i < rest.length; i += 1) {
    const arg = rest[i];
    if (arg === "--out") {
      outPath = rest[i + 1];
      if (!outPath) {
        console.error("missing value for --out");
        return 2;
      }
      i += 1;
      continue;
    }
    if (typeof arg === "string" && arg.startsWith("--out=")) {
      outPath = arg.slice(6);
      continue;
    }
    if (arg === "--created-at") {
      createdAt = rest[i + 1];
      if (!createdAt) {
        console.error("missing value for --created-at");
        return 2;
      }
      i += 1;
      continue;
    }
    if (typeof arg === "string" && arg.startsWith("--created-at=")) {
      createdAt = arg.slice("--created-at=".length);
      continue;
    }
    console.error(`unrecognized option for expand: ${arg}`);
    return 2;
  }
  if (!outPath) {
    console.error("tf expand requires --out <FILE>");
    return 2;
  }

  let existing = null;
  if (fs.existsSync(outPath)) {
    try {
      existing = JSON.parse(fs.readFileSync(outPath, "utf8"));
    } catch {
      existing = null;
    }
  }

  const options = {};
  if (createdAt) {
    options.createdAt = createdAt;
  } else if (existing?.created_at) {
    options.createdAt = existing.created_at;
  }

  const pipeline = expandPipelineFromFile(input, options);
  fs.mkdirSync(path.dirname(outPath), { recursive: true });
  fs.writeFileSync(outPath, `${JSON.stringify(pipeline, null, 2)}\n`, "utf8");
  return 0;
}

async function runCheckCommand(rawArgs) {
  const argv = Array.isArray(rawArgs) ? [...rawArgs] : [];
  if (argv.length === 0) {
    console.error(
      "usage: tf check <L0_FILE> [--summary] [--json] [--policy <path>] [--caps <path>] [--out <path>]"
    );
    return 2;
  }

  let summaryMode = false;
  let jsonMode = false;
  let policyPath;
  let capsPath;
  let outPath;
  const files = [];

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--summary") {
      summaryMode = true;
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

    const outHit = consumeFlagWithValue(argv, i, "out");
    if (outHit) {
      if (outHit.err) return outHit.err;
      outPath = outHit.value;
      i = outHit.i;
      continue;
    }

    files.push(arg);
  }

  if (files.length !== 1) {
    console.error(
      "usage: tf check <L0_FILE> [--summary] [--json] [--policy <path>] [--caps <path>] [--out <path>]"
    );
    return 2;
  }

  const [file] = files;
  const options = {};
  if (policyPath) options.policyPath = policyPath;
  if (capsPath) options.capsPath = capsPath;

  let report;
  try {
    report = await checkL0(file, options);
  } catch (error) {
    console.error(`${file}: ${error?.message ?? error}`);
    return 1;
  }

  if (outPath) {
    try {
      fs.mkdirSync(path.dirname(outPath), { recursive: true });
      fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, "utf8");
    } catch (error) {
      console.error(`failed to write report to ${outPath}: ${error?.message ?? error}`);
      return 1;
    }
  }

  if (jsonMode) {
    console.log(JSON.stringify(report, null, 2));
  } else if (summaryMode) {
    console.log(formatCheckSummary(report, { file }));
  } else {
    const location = displayPath(file);
    const label = location ? `${location}` : file;
    console.log(`Check ${label}: ${report.status ?? "UNKNOWN"}`);
    console.log("Use --summary or --json for detailed output.");
  }

  return report.status === "GREEN" ? 0 : 1;
}

function formatTraceValue(value) {
  if (value === undefined) return "undefined";
  try {
    const serialized = JSON.stringify(value);
    if (!serialized) {
      return String(value);
    }
    return serialized.length > 160 ? `${serialized.slice(0, 157)}...` : serialized;
  } catch {
    return String(value);
  }
}

async function runRuntimeExecCommand(argv) {
  const args = Array.isArray(argv) ? [...argv] : [];
  let traceMode = false;
  const files = [];

  for (const arg of args) {
    if (arg === "--trace") {
      traceMode = true;
      continue;
    }
    files.push(arg);
  }

  if (files.length !== 1) {
    console.error("usage: tf runtime exec <L0_FILE> [--trace]");
    return 2;
  }

  const [file] = files;

  let pipeline;
  try {
    pipeline = await loadJsonFile(file);
  } catch (error) {
    console.error(`${file}: ${error?.message ?? error}`);
    return 1;
  }

  const sanitized = JSON.parse(JSON.stringify(pipeline));
  const schemaNotes = [];
  if (Array.isArray(sanitized.nodes)) {
    for (const node of sanitized.nodes) {
      if (
        node
        && node.kind === "Transform"
        && node.spec?.op === "jsonschema.validate"
        && typeof node.spec.schema === "string"
      ) {
        schemaNotes.push({ id: node.id ?? null, schema: node.spec.schema });
      }
    }
  }

  const restoreHandlers = [];
  if (schemaNotes.length > 0) {
    const original = getTransform("jsonschema.validate");
    if (typeof original === "function") {
      const unregister = registerTransform("jsonschema.validate", (spec, input) => {
        if (typeof spec.schema === "string") {
          return input?.value ?? input?.data ?? input;
        }
        return original(spec, input);
      });
      restoreHandlers.push(unregister);
    }
  }

  try {
    const { trace } = await executeL0(sanitized, { ignoreTimeouts: true });
    console.log("Runtime execution OK");
    if (!traceMode) {
      return 0;
    }

    if (schemaNotes.length > 0) {
      console.log(
        `Schema placeholders applied for ${schemaNotes
          .map((entry) => `${entry.id ?? '(node)'}→${entry.schema}`)
          .join(', ')}`
      );
    }

    console.log(`Variables (${trace.variables.length})`);
    for (const entry of trace.variables ?? []) {
      const parts = [` - ${entry.var}`];
      if (entry.node) parts.push(`← ${entry.node}`);
      if (entry.kind) parts.push(`[${entry.kind}]`);
      if (entry.op) parts.push(`op=${entry.op}`);
      parts.push(`value=${formatTraceValue(entry.value)}`);
      console.log(parts.join(' '));
    }

    console.log(`Transforms (${trace.transforms.length})`);
    for (const transform of trace.transforms ?? []) {
      const label = transform.outVar ? `${transform.id ?? '(node)'} → ${transform.outVar}` : transform.id ?? '(node)';
      const opText = transform.op ? ` op=${transform.op}` : '';
      const determinism = transform.deterministic === false
        ? ' [non-deterministic]'
        : transform.deterministic === true
          ? ' [deterministic]'
          : '';
      console.log(` - ${label}${opText}${determinism} result=${formatTraceValue(transform.result)}`);
    }

    console.log(`Subscribes (${trace.subscribes.length})`);
    for (const sub of trace.subscribes ?? []) {
      const varText = sub.outVar ? ` → ${sub.outVar}` : '';
      const errorText = sub.error ? ` error=${sub.error}` : '';
      console.log(` - ${sub.id ?? '(node)'}${varText} channel=${sub.channel}${errorText}`);
    }

    console.log(`Publishes (${trace.publishes.length})`);
    for (const pub of trace.publishes ?? []) {
      const errorText = pub.error ? ` error=${pub.error}` : '';
      console.log(` - ${pub.id ?? '(node)'} → ${pub.channel}${errorText}`);
    }

    console.log(`Keypairs (${trace.keypairs.length})`);
    for (const kp of trace.keypairs ?? []) {
      const varText = kp.outVar ? ` → ${kp.outVar}` : '';
      console.log(` - ${kp.id ?? '(node)'}${varText} algorithm=${kp.algorithm}`);
    }

    return 0;
  } catch (error) {
    console.error(`runtime exec failed: ${error?.message ?? error}`);
    return 1;
  } finally {
    for (const restore of restoreHandlers) {
      try {
        restore();
      } catch {
        /* noop */
      }
    }
  }
}

/* --------------------------------- Usage ---------------------------------- */

function printMainHelp(exitCode = 0) {
  const lines = [
    "usage: tf <command> [options]",
    "",
    "Core commands:",
    "  plan             Summarize runtime instance selections (alias: plan-instances)",
    "  expand           Expand an L2 YAML pipeline into L0 JSON",
    "  check            Validate an L0 pipeline against policy, capabilities, and laws",
    "  typecheck        Verify port bindings and suggest/emit adapters",
    "  laws             Inspect prover goals or capture solver evidence",
    "  runtime exec     Execute an L0 pipeline with in-memory adapters",
    "",
    "Utilities:",
    "  validate         Validate L0/L2 JSON against schemas",
    "  effects          Summarize declared vs computed effects",
    "  graph            Emit a DOT graph for an L0 pipeline",
    "  open             List checkpoint phases for a rulebook node",
    "  explain          Explain which checkpoint rules fire for a phase",
    "  run              Execute checkpoint rules and emit TFREPORT.json",
    "",
    "Run `tf <command> --help` for command-specific usage."
  ];
  console.log(lines.join("\n"));
  process.exit(exitCode);
}

function printPlanHelp(exitCode = 0) {
  const lines = [
    "usage: tf plan [--registry <path>] [--group-by domain|scheme] [--format json|table] [--explain] <L0_FILE>",
    "       tf plan-instances … (alias)",
    "",
    "Summarize runtime.instance selections by domain or channel scheme.",
    "Use --registry to try alternate deployment registries and --explain for per-node details."
  ];
  console.log(lines.join("\n"));
  process.exit(exitCode);
}

function printExpandHelp(exitCode = 0) {
  const lines = [
    "usage: tf expand <PIPELINE.l2.yaml> --out <PIPELINE.l0.json> [--created-at <iso8601>]",
    "",
    "Compile an L2 YAML pipeline into an immutable L0 DAG.",
    "If --created-at is omitted, the previous artifact timestamp is reused when available."
  ];
  console.log(lines.join("\n"));
  process.exit(exitCode);
}

function printCheckHelp(exitCode = 0) {
  const lines = [
    "usage: tf check <L0_FILE> [--summary] [--json] [--policy <path>] [--caps <path>] [--out <path>]",
    "",
    "Validate effects, policy bindings, capabilities, and law goals for an L0 pipeline.",
    "--summary prints a human-readable rollup; --json emits the full report to stdout."
  ];
  console.log(lines.join("\n"));
  process.exit(exitCode);
}

/* --------------------------------- Main ----------------------------------- */

(async function main() {
  const [cmd, ...argv] = process.argv.slice(2);
  if (!cmd) printMainHelp(2);

  if (cmd === "--help" || cmd === "-h") {
    printMainHelp(0);
  }

  if (cmd === "help") {
    printMainHelp(0);
  }

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

  if ((cmd === "plan" || cmd === "plan-instances") && argv.length === 1 && ["--help", "-h"].includes(argv[0])) {
    printPlanHelp(0);
  }

  if (cmd === "plan" || cmd === "plan-instances") {
    const code = await runPlanInstancesCommand(argv);
    process.exit(code);
  }

  if (cmd === "check" && argv.length === 1 && ["--help", "-h"].includes(argv[0])) {
    printCheckHelp(0);
  }

  if (cmd === "check") {
    const code = await runCheckCommand(argv);
    process.exit(code);
  }

  if (cmd === "laws") {
    const code = await runLawsCommand(argv);
    process.exit(code);
  }

  if (cmd === "expand" && argv.length === 1 && ["--help", "-h"].includes(argv[0])) {
    printExpandHelp(0);
  }

  if (cmd === "expand") {
    const code = runExpandCommand(argv);
    process.exit(code);
  }

  if (cmd === "runtime") {
    const [subcmd, ...rest] = argv;
    if (subcmd !== "exec") {
      console.error("usage: tf runtime exec <L0_FILE> [--trace]");
      process.exit(2);
    }
    const code = await runRuntimeExecCommand(rest);
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

  printMainHelp(2);
})().catch((e) => {
  console.error(e?.message ?? e);
  process.exit(99);
});
