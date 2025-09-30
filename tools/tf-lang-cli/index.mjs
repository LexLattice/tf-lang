#!/usr/bin/env node
import fs from "fs";
import path from "path";
import { spawnSync, execSync } from "child_process";
import { loadRulebookPlan, rulesForPhaseFromPlan } from "./expand.mjs";

function graphLabel(value) {
  return String(value).replace(/"/g, "\\\"");
}

function renderPipelineGraph(doc) {
  const nodes = doc.nodes ?? [];
  const lines = [];
  lines.push("digraph G {");
  lines.push("  rankdir=LR;");
  nodes.forEach((node, idx) => {
    let label;
    switch (node.kind) {
      case "Subscribe":
      case "Publish":
        label = `${node.id}\n${node.channel}`;
        break;
      case "Transform":
        label = `${node.id}\n${node.spec?.op ?? ""}`;
        break;
      case "Keypair":
        label = `${node.id}\n${node.algorithm}`;
        break;
      default:
        label = node.id;
    }
    lines.push(`  n${idx} [label="${graphLabel(label)}"];`);
    if (idx > 0) {
      lines.push(`  n${idx - 1} -> n${idx};`);
    }
  });
  lines.push("}");
  return lines.join("\n");
}

function renderMonitorGraph(doc) {
  const lines = [];
  const monitors = doc.monitors ?? [];
  lines.push("digraph G {");
  lines.push("  rankdir=LR;");
  monitors.forEach((monitor, monitorIndex) => {
    const clusterName = `cluster_${monitorIndex}`;
    lines.push(`  subgraph ${clusterName} {`);
    lines.push(`    label="${graphLabel(monitor.monitor_id ?? `monitor_${monitorIndex}`)}";`);
    let prevName = null;
    (monitor.nodes ?? []).forEach((node, nodeIndex) => {
      const nodeName = `m${monitorIndex}_n${nodeIndex}`;
      const label = `${node.id}\n${node.kind}`;
      lines.push(`    ${nodeName} [label="${graphLabel(label)}"];`);
      if (prevName) {
        lines.push(`    ${prevName} -> ${nodeName};`);
      }
      prevName = nodeName;
    });
    lines.push("  }");
  });
  lines.push("}");
  return lines.join("\n");
}

function collectKernelNodes(doc) {
  if (Array.isArray(doc.nodes)) return doc.nodes;
  if (Array.isArray(doc.monitors)) return doc.monitors.flatMap((m) => m.nodes ?? []);
  throw new Error("unsupported document for effects");
}

function summarizeEffects(doc) {
  const nodes = collectKernelNodes(doc);
  const seen = new Set();
  nodes.forEach((node) => {
    switch (node.kind) {
      case "Publish":
        seen.add("Outbound");
        break;
      case "Subscribe":
        seen.add("Inbound");
        break;
      case "Keypair":
        seen.add("Entropy");
        break;
      case "Transform":
        seen.add("Pure");
        break;
      default:
        throw new Error(`unsupported kernel kind: ${node.kind}`);
    }
  });
  const order = ["Outbound", "Inbound", "Entropy", "Pure"];
  const parts = order.filter((item) => seen.has(item));
  if (parts.length === 0) return "Pure";
  return parts.join("+");
}

function rbPath(node) {
  const p = path.join("tf", "blocks", node, "rulebook.yml");
  if (!fs.existsSync(p)) throw new Error(`missing rulebook: ${p}`);
  return p;
}

function resolveRulebookPath(input) {
  if (!input) return null;
  if (input.includes("/") || input.endsWith(".yml") || input.endsWith(".yaml")) {
    if (!fs.existsSync(input)) {
      throw new Error(`missing rulebook: ${input}`);
    }
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
    maxBuffer: 10 * 1024 * 1024,
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
  if (!selected) {
    throw new Error(`unknown phase "${targetPhase}"`);
  }

  const payload = {
    phase: selected.id,
    inherits: [...selected.inherits],
    rules: selected.rules.map((rule) => ({ ...rule })),
  };

  process.stdout.write(`${JSON.stringify(payload, null, 2)}\n`);
}

function usage() {
  console.log("usage: tf-lang <open|run|explain> ...");
  process.exit(2);
}

(async function main() {
  const [cmd, ...argv] = process.argv.slice(2);

  if (!cmd) {
    usage();
  }

  if (cmd === "open") {
    const [node] = argv;
    if (!node) {
      console.error("usage: tf-lang open <NODE>");
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
      console.error("usage: tf-lang explain <rulebook.yml|NODE> <PHASE>");
      process.exit(2);
    }
    const rulebookPath = resolveRulebookPath(rulebookArg);
    const plan = loadRulebookPlan(rulebookPath);
    explainPlan(plan, phaseId);
    process.exit(0);
  }

  if (cmd === "graph") {
    const [inputPath] = argv;
    if (!inputPath) {
      console.error("usage: tf-lang graph <pipeline-or-monitor.l0.json>");
      process.exit(2);
    }
    const doc = JSON.parse(fs.readFileSync(inputPath, "utf8"));
    if (Array.isArray(doc.nodes)) {
      console.log(renderPipelineGraph(doc));
    } else if (Array.isArray(doc.monitors)) {
      console.log(renderMonitorGraph(doc));
    } else {
      throw new Error("unsupported graph document shape");
    }
    process.exit(0);
  }

  if (cmd === "effects") {
    const [inputPath] = argv;
    if (!inputPath) {
      console.error("usage: tf-lang effects <pipeline-or-monitor.l0.json>");
      process.exit(2);
    }
    const doc = JSON.parse(fs.readFileSync(inputPath, "utf8"));
    console.log(summarizeEffects(doc));
    process.exit(0);
  }

  if (cmd === "run") {
    const [node, cp, ...rest] = argv;
    if (!node || !cp) {
      console.error("usage: tf-lang run <NODE> <CP> [--diff -] [--explain]");
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
    if (rest.includes("--explain")) {
      explainPlan(plan, cp);
    }
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
      if (!command) {
        results[r.id] = { ok: false, reason: "unsupported-kind" };
        continue;
      }
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
      evidence,
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
