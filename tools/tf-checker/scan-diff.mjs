#!/usr/bin/env node
import fs from "node:fs";
import * as yaml from "yaml";
import picomatch from "picomatch";

const readStdin = () =>
  new Promise(resolve => {
    let data = "";
    process.stdin.setEncoding("utf8");
    process.stdin.on("data", chunk => (data += chunk));
    process.stdin.on("end", () => resolve(data));
  });

const compileGlobs = (patterns = []) =>
  patterns.map(glob => picomatch(glob, { dot: true }));

const matchesAny = (matchers, file) =>
  matchers.length > 0 && matchers.some(match => match(file));

const globs = patterns => {
  const matchers = compileGlobs(patterns || []);
  return file => (matchers.length === 0 ? true : matchers.some(match => match(file)));
};

function parseDiff(text) {
  if (!text) return [];
  const out = [];
  let current = null;
  let nextLine = 0;
  const lines = text.split("\n");

  for (const line of lines) {
    if (line.startsWith("+++ ")) {
      const file = line.replace("+++ b/", "").replace("+++ ", "");
      if (current) out.push(current);
      current = { file, added: [] };
      continue;
    }

    if (line.startsWith("@@")) {
      const match = /@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@/.exec(line);
      nextLine = match ? parseInt(match[1], 10) : 0;
      continue;
    }

    if (!current) continue;

    if (line.startsWith("+") && !line.startsWith("+++")) {
      current.added.push({ ln: nextLine, text: line.slice(1) });
      nextLine++;
    } else if (line.startsWith(" ")) {
      nextLine++;
    } else if (line.startsWith("diff --git ")) {
      out.push(current);
      current = null;
    }
  }

  if (current) out.push(current);
  out.forEach(f => (f.file = f.file.replace(/^b\//, "")));
  return out;
}

function scan(diff, cfg) {
  const allow = globs(cfg.allow_paths);
  const forbid = globs(cfg.forbid_paths);
  const tokenRules = (cfg.token_rules || []).map(rule => ({
    ...rule,
    include: globs(rule.include || ["**/*"]),
    exclude: globs(rule.exclude || []),
    rx: new RegExp(rule.pattern, "g")
  }));

  const scopeViolations = [];
  const tokenViolations = [];
  const tokenWarnings = [];
  const touched = new Set(diff.map(f => f.file));

  for (const file of touched) {
    const withinScope = allow(file);
    const forbidden = forbid(file);
    if (!withinScope || forbidden) {
      scopeViolations.push({
        file,
        reason: !withinScope ? "not in allow_paths" : "in forbid_paths"
      });
    }
  }

  for (const file of diff) {
    for (const rule of tokenRules) {
      if (!rule.include(file.file) || rule.exclude(file.file)) continue;
      for (const added of file.added) {
        rule.rx.lastIndex = 0;
        if (rule.rx.test(added.text)) {
          const hit = {
            rule_id: rule.id,
            file: file.file,
            ln: added.ln,
            snippet: added.text.trim()
          };
          (rule.severity === "block" ? tokenViolations : tokenWarnings).push(hit);
        }
      }
    }
  }

  const strict = process.env.TF_STRICT === "1";
  const ok =
    scopeViolations.length === 0 &&
    tokenViolations.length === 0 &&
    (strict ? tokenWarnings.length === 0 : true);

  return {
    ok,
    allowed_scope_ok: scopeViolations.length === 0,
    forbidden_paths_violations: scopeViolations,
    token_violations: tokenViolations,
    token_warnings: tokenWarnings,
    touched_files: Array.from(touched).sort(),
    stats: {
      files: diff.length,
      added_lines: diff.reduce((total, file) => total + file.added.length, 0)
    }
  };
}

(async function main() {
  const args = process.argv.slice(2);
  const getValue = flag => {
    const idx = args.indexOf(flag);
    if (idx === -1) return null;
    const value = args[idx + 1];
    return value && !value.startsWith("-") ? value : null;
  };
  const getAll = flag => {
    const values = [];
    let idx = -1;
    while ((idx = args.indexOf(flag, idx + 1)) !== -1) {
      const value = args[idx + 1];
      if (value && !value.startsWith("-")) values.push(value);
    }
    return values;
  };

  const configPath = getValue("--config") || "meta/checker.yml";
  const diffArg = getValue("--diff");
  const allowPatterns = getAll("--allow");
  const forbidPatterns = getAll("--forbid");

  const config = yaml.parse(fs.readFileSync(configPath, "utf8"));

  let diffText = "";
  if (diffArg === "-") {
    diffText = await readStdin();
  } else if (diffArg) {
    diffText = fs.readFileSync(diffArg, "utf8");
  }

  const files = parseDiff(diffText);
  const report = scan(files, config);

  const allowMatchers = compileGlobs(allowPatterns);
  const forbidMatchers = compileGlobs(forbidPatterns);

  if (Array.isArray(report.forbidden_paths_violations) && allowMatchers.length) {
    report.forbidden_paths_violations = report.forbidden_paths_violations.filter(
      violation => !matchesAny(allowMatchers, violation.file)
    );
  }

  if (forbidMatchers.length && Array.isArray(report.touched_files)) {
    const extras = report.touched_files
      .filter(file => matchesAny(forbidMatchers, file))
      .map(file => ({ file, reason: "explicitly forbidden via --forbid" }));
    if (extras.length) {
      report.forbidden_paths_violations = (report.forbidden_paths_violations || []).concat(extras);
    }
  }

  const noForbidden = !(report.forbidden_paths_violations && report.forbidden_paths_violations.length);
  report.allowed_scope_ok = noForbidden && report.allowed_scope_ok !== false;

  const strict = process.env.TF_STRICT === "1";
  if (strict && Array.isArray(report.token_warnings) && report.token_warnings.length) {
    report.ok = false;
  }

  if (noForbidden && report.ok !== false) {
    report.ok = true;
  }

  process.stdout.write(JSON.stringify(report, null, 2) + "\n");
  process.exitCode = report.ok ? 0 : 2;
})().catch(err => {
  console.error(err);
  process.exit(99);
});
