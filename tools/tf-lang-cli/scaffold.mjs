#!/usr/bin/env node
// ESM scaffolder for tf-lang 0.45
import fs from "node:fs";
import path from "node:path";

const args = process.argv.slice(2);
const NODE_ID = args[0];
if (!NODE_ID) {
  console.error("usage: node tools/tf-lang-cli/scaffold.mjs <NODE_ID> [--no-vscode]");
  process.exit(2);
}
const NO_VSCODE = args.includes("--no-vscode");

function ensureDir(p) { fs.mkdirSync(p, { recursive: true }); }
function writeIfMissing(p, content) {
  if (fs.existsSync(p)) {
    console.log("exists:", p);
    return false;
  }
  ensureDir(path.dirname(p));
  fs.writeFileSync(p, content, "utf8");
  console.log("created:", p);
  return true;
}

const checkerYml = () => `version: 1
allow_paths:
  - "packages/tf-lsp-server/**"
  - "clients/vscode-tf/**"
forbid_paths:
  - "packages/tf-optimize/**"
  - "crates/**"
  - "**/*.generated.*"

token_rules:
  - id: ts_any_type
    desc: "TypeScript ': any'"
    include: ["**/*.ts","**/*.tsx"]
    exclude: ["**/*.d.ts","**/__tests__/**","**/test/**"]
    pattern: ":\\\\s*any\\\\b"
    severity: block
  - id: ts_as_any
    desc: "TypeScript 'as any'"
    include: ["**/*.ts","**/*.tsx"]
    pattern: "\\\\bas\\\\s+any\\\\b"
    severity: block
  - id: js_eval
    desc: "eval()"
    include: ["**/*.js","**/*.ts","**/*.tsx"]
    pattern: "\\\\beval\\\\s*\\\\("
    severity: block
  - id: ts_ignore
    desc: "@ts-ignore"
    include: ["**/*.ts","**/*.tsx"]
    pattern: "@ts-ignore"
    severity: warn

strict: false
`;

const tfYaml = (node) => `id: ${node}
version: 0.45.0
scope:
  allow_paths: ["packages/tf-lsp-server/**","clients/vscode-tf/**"]
  forbid_paths: ["**/*.generated.*","crates/**"]
notes:
  - "Acceptance lives in rulebook.yml phases"
`;

const rulebookYml = (node) => `version: 1
meta: { node: ${node}, title: "${node} rulebook" }

phases:
  cp1_baseline:
    title: "Baseline: build + scope"
    inherits: []
    rules: [compile_ok, scope_guard, banned_tokens_soft]

  cp2_diag:
    title: "Diagnostics with ranges"
    inherits: [cp1_baseline]
    rules: [diag_ranges]

  cp3_hover:
    title: "Hover: signature/effects/laws"
    inherits: [cp2_diag]
    rules: [hover_signatures]

  cp4_code_actions:
    title: "CodeAction: Wrap with Authorize{scope=?}"
    inherits: [cp3_hover]
    rules: [code_action_authorize, banned_tokens_hard]

rules:
  compile_ok:
    kind: probe.exec
    command: "pnpm -w -r build --silent"
    expect: { exit_code: 0 }

  scope_guard:
    kind: probe.exec
    command: "cat \\"$DIFF_PATH\\" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff -"
    expect: { jsonpath_eq: { "$.ok": true } }

  banned_tokens_soft:
    kind: probe.exec
    command: "cat \\"$DIFF_PATH\\" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff -"
    expect: { jsonpath_eq: { "$.token_violations.length": 0 } }

  banned_tokens_hard:
    kind: probe.exec
    env: { TF_STRICT: "1" }
    command: "cat \\"$DIFF_PATH\\" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff -"
    expect: { jsonpath_eq: { "$.token_warnings.length": 0 } }

  diag_ranges:
    kind: probe.exec
    command: "node scripts/probe-lsp-diag.mjs"
    expect: { jsonpath: "$.diagnostics[*].range", nonempty: true }

  hover_signatures:
    kind: probe.exec
    command: "node scripts/probe-lsp-hover.mjs tf:network/publish@1"
    expect: { jsonpath_all: ["$.signature","$.effects","$.laws"] }

  code_action_authorize:
    kind: probe.exec
    command: "node scripts/probe-lsp-codeaction.mjs samples/illegal_write.tf"
    expect: { contains: "Authorize{scope" }
`;

const validateTf = () => `# optional TF wrapper (0.45 can use CLI directly)
# Seq {
#   tf:ci/check_scope@1 { diff_path = env.DIFF_PATH, config = "meta/checker.yml" }
#   tf:rules/expand@1 { rulebook = "tf/blocks/${NODE_ID}/rulebook.yml", checkpoint = input.checkpoint }
#   tf:ci/run_selected_probes@1 { selected = "out/rules.selected.json", artifacts = input.artifacts }
#   tf:report/emit@1 { out = "out/TFREPORT.json" }
# }
`;

const cliIndex = () => `#!/usr/bin/env node
import fs from "fs"; import path from "path"; import yaml from "yaml";
import { spawnSync, execSync } from "child_process";
import { rulesForPhase } from "./expand.mjs";

function rbPath(node){ const p=path.join("tf","blocks",node,"rulebook.yml"); if(!fs.existsSync(p)) throw new Error("missing rulebook: "+p); return p; }
function writeDiff(text){ fs.mkdirSync("out/tmp",{recursive:true}); const p="out/tmp/latest.diff"; fs.writeFileSync(p,text,"utf8"); return path.resolve(p); }
function run(cmd, env){ const r=spawnSync(cmd,{shell:true,encoding:"utf8",env:{...process.env,...env},maxBuffer:10*1024*1024}); return { code:r.status??99, stdout:(r.stdout||"").trim(), stderr:(r.stderr||"").trim() }; }
function check(res, expect){
  if(!expect) return { ok: res.code===0 };
  if(expect.exit_code!==undefined) return { ok: res.code===expect.exit_code };
  if(expect.contains) return { ok: (res.stdout||"").includes(expect.contains)||(res.stderr||"").includes(expect.contains) };
  if(expect.jsonpath_eq){ try{ const j=JSON.parse(res.stdout||"{}"); const k=Object.keys(expect.jsonpath_eq)[0]; const key=k.replace(/^\\$\\./,""); const want=expect.jsonpath_eq[k]; return { ok: JSON.stringify(j[key])===JSON.stringify(want) }; } catch{} }
  if(expect.nonempty){ try{ const j=JSON.parse(res.stdout||"{}"); return { ok: Object.keys(j).length>0 }; } catch{} }
  return { ok: res.code===0 };
}

(async function main(){
  const [cmd, node, cp, ...rest] = process.argv.slice(2);
  if(cmd==="open"){
    if(!node){ console.error("usage: tf-lang open <NODE>"); process.exit(2); }
    const rb=yaml.parse(fs.readFileSync(rbPath(node),"utf8"));
    console.log("Node:", node); console.log("Phases:", Object.keys(rb.phases).join(", "));
    process.exit(0);
  }
  if(cmd==="run"){
    if(!node||!cp){ console.error("usage: tf-lang run <NODE> <CP> [--diff -]"); process.exit(2); }
    let diff=""; if(rest.includes("--diff") && rest[rest.indexOf("--diff")+1]==="-") diff=fs.readFileSync(0,"utf8"); else {
      try { diff = execSync("git diff -U0 --no-color", {encoding:"utf8"}); } catch { diff=""; }
    }
    const diffPath = writeDiff(diff);
    const selected = rulesForPhase(rbPath(node), cp);
    const results = {}; const evidence=[];
    for(const r of selected){
      if(r.kind!=="probe.exec"){ results[r.id]={ok:false,reason:"unsupported-kind"}; continue; }
      const res = run(r.command, { ...(r.env||{}), DIFF_PATH: diffPath });
      const ch = check(res, r.expect || {});
      results[r.id] = { ok: ch.ok, code: res.code, reason: ch.reason || null };
      evidence.push({ id: r.id, cmd: r.command, code: res.code, out: (res.stdout||"").slice(0,2000) });
      if(!ch.ok) console.error(\`[FAIL] \${r.id} — \${r.command}\`);
    }
    const report = { contract_id: \`\${node}@0.45\`, node_id: node, checkpoint: cp, timestamp: new Date().toISOString(), results, evidence };
    fs.mkdirSync("out",{recursive:true}); fs.writeFileSync("out/TFREPORT.json", JSON.stringify(report, null, 2));
    const ok = Object.values(results).every(v => v.ok);
    console.log(\`\\nRESULT: \${ok ? "GREEN" : "RED"}  (\${Object.keys(results).length} probes)\`); process.exit(ok?0:3);
  }
  if(!["open","run"].includes(cmd)){
    console.log("usage: tf-lang <open|run> ..."); process.exit(2);
  }
})().catch(e=>{ console.error(e); process.exit(99); });
`;

const cliExpand = () => `import fs from "fs"; import yaml from "yaml";
export function rulesForPhase(rulebookPath, phaseId) {
  const rb = yaml.parse(fs.readFileSync(rulebookPath, "utf8"));
  const seen = new Set(); const ordered = [];
  function addPhase(pid) {
    const p = rb.phases[pid]; if (!p) throw new Error(\`unknown phase \${pid}\`);
    for (const inh of (p.inherits||[])) addPhase(inh);
    for (const id of (p.rules||[])) if (!seen.has(id)) { seen.add(id); ordered.push({ id, ...rb.rules[id] }); }
  }
  addPhase(phaseId); return ordered;
}
`;

const scanDiff = () => `#!/usr/bin/env node
import fs from "node:fs"; import * as yaml from "yaml"; import picomatch from "picomatch";
const readStdin = () => new Promise(r => { let d=""; process.stdin.setEncoding("utf8"); process.stdin.on("data",c=>d+=c); process.stdin.on("end",()=>r(d)); });
function globs(ps){ const ms=(ps||[]).map(g=>picomatch(g,{dot:true})); return f=>ms.length===0||ms.some(m=>m(f)); }
function parseDiff(t){ const out=[]; let cur=null,nl=0; const L=t.split("\\n");
  for(const line of L){
    if(line.startsWith("+++ ")){ const b=line.replace("+++ b/","").replace("+++ ",""); if(cur) out.push(cur); cur={file:b,added:[]}; continue; }
    if(line.startsWith("@@")){ const m=/@@ -\\d+(?:,\\d+)? \\+(\\d+)(?:,(\\d+))? @@/.exec(line); nl=m?parseInt(m[1],10):0; continue; }
    if(!cur) continue;
    if(line.startsWith("+")&&!line.startsWith("+++")){ cur.added.push({ln:nl,text:line.slice(1)}); nl++; }
    else if(line.startsWith(" ")) nl++;
    else if(line.startsWith("diff --git ")){ out.push(cur); cur=null; }
  } if(cur) out.push(cur); out.forEach(f=>f.file=f.file.replace(/^b\\//,"")); return out;
}
function scan(diff, cfg){
  const allow=globs(cfg.allow_paths), forbid=globs(cfg.forbid_paths);
  const rules=(cfg.token_rules||[]).map(r=>({...r, include:globs(r.include||["**/*"]), exclude:globs(r.exclude||[]), rx:new RegExp(r.pattern,"g")}));
  const scope=[], viol=[], warn=[];
  const touched=new Set(diff.map(f=>f.file));
  for(const f of touched){ const ok=allow(f), bad=forbid(f); if(!ok||bad) scope.push({file:f, reason:!ok?"not in allow_paths":"in forbid_paths"}); }
  for(const f of diff) for(const r of rules){
    if(!r.include(f.file)||r.exclude(f.file)) continue;
    for(const a of f.added){ r.rx.lastIndex=0; if(r.rx.test(a.text)){ const hit={rule_id:r.id,file:f.file,ln:a.ln,snippet:a.text.trim()}; (r.severity==="block"?viol:warn).push(hit); } }
  }
  const ok=scope.length===0 && viol.length===0 && ((process.env.TF_STRICT==="1")?warn.length===0:true);
  return { ok, allowed_scope_ok:scope.length===0, forbidden_paths_violations:scope, token_violations:viol, token_warnings:warn,
           stats:{files:diff.length,added_lines:diff.reduce((n,f)=>n+f.added.length,0)} };
}
(async function main(){
  const args=process.argv.slice(2); const cfgPath=args.includes("--config")?args[args.indexOf("--config")+1]:"meta/checker.yml";
  const cfg=yaml.parse(fs.readFileSync(cfgPath,"utf8"));
  const diffText=args.includes("--diff")&&args[args.indexOf("--diff")+1]==="-" ? await readStdin() : "";
  const files=parseDiff(diffText);
  const report=scan(files,cfg); process.stdout.write(JSON.stringify(report,null,2)+"\\n"); process.exitCode=report.ok?0:2;
})().catch(e=>{ console.error(e); process.exit(99); });
`;

const probeDiag = () => `#!/usr/bin/env node
console.log(JSON.stringify({ diagnostics: [ { range:{ start:{line:1,col:1}, end:{line:1,col:5} }, msg:"stub" } ] }));
`;
const probeHover = () => `#!/usr/bin/env node
console.log(JSON.stringify({ signature:"pub(topic:string)", effects:["Network.Out"], laws:["obs_pure_commute"] }));
`;
const probeAction = () => `#!/usr/bin/env node
console.log("Quick Fix: Wrap with Authorize{scope:\\"\\\\"}");
`;

const workflow = () => `name: tf-lang checkpoint
on: [pull_request]
jobs:
  checkpoint:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: pnpm/action-setup@v4
        with: { version: 9 }
      - uses: actions/setup-node@v4
        with: { node-version: 20 }
      - run: pnpm -w -r install
      - name: Extract node/cp from PR title (format: 'node:<ID> cp:<PHASE>')
        id: meta
        run: |
          T="\${{ github.event.pull_request.title }}"
          NODE=$(echo "$T" | sed -n 's/.*node:\\([A-Za-z0-9._-]\\+\\).*/\\1/p')
          CP=$(echo "$T" | sed -n 's/.*cp:\\([A-Za-z0-9._-]\\+\\).*/\\1/p')
          echo "node=$NODE" >> $GITHUB_OUTPUT
          echo "cp=$CP" >> $GITHUB_OUTPUT
      - name: Validate meta
        run: |
          [ -n "\${{ steps.meta.outputs.node }}" ] && [ -n "\${{ steps.meta.outputs.cp }}" ] || { echo "PR title must contain 'node:<ID> cp:<PHASE>'"; exit 1; }
      - name: Get PR diff
        run: gh pr diff \${{ github.event.pull_request.number }} --patch --color=never > out/tmp/pr.diff
        env: { GITHUB_TOKEN: \${{ secrets.GITHUB_TOKEN }} }
      - name: Run checkpoint
        run: cat out/tmp/pr.diff | node tools/tf-lang-cli/index.mjs run \${{ steps.meta.outputs.node }} \${{ steps.meta.outputs.cp }} --diff -
      - uses: actions/upload-artifact@v4
        with:
          name: TFREPORT
          path: out/TFREPORT.json
`;

const vscodeTasks = (node) => `{
  "version": "2.0.0",
  "tasks": [
    {
      "label": "TF: Run checkpoint (${node} cp1_baseline)",
      "type": "shell",
      "command": "git diff -U0 --no-color | node tools/tf-lang-cli/index.mjs run ${node} cp1_baseline --diff -",
      "problemMatcher": []
    }
  ]
}
`;

const pkgPatch = () => {
  const pkgPath = "package.json";
  if (!fs.existsSync(pkgPath)) return;
  const pkg = JSON.parse(fs.readFileSync(pkgPath, "utf8"));
  pkg.scripts = {
    ...(pkg.scripts || {}),
    "tf:new-node": "node tools/tf-lang-cli/scaffold.mjs",
    "tf:open": "node tools/tf-lang-cli/index.mjs open",
    "tf:run": "node tools/tf-lang-cli/index.mjs run"
  };
  pkg.devDependencies = {
    ...(pkg.devDependencies || {}),
    "yaml": pkg.devDependencies?.yaml || "^2.4.5",
    "picomatch": pkg.devDependencies?.picomatch || "^4.0.2"
  };
  fs.writeFileSync(pkgPath, JSON.stringify(pkg, null, 2));
  console.log("patched:", pkgPath, "(scripts + devDependencies)");
};

// Write base files (idempotent)
writeIfMissing("meta/checker.yml", checkerYml());
writeIfMissing(`tf/blocks/${NODE_ID}/TF.yaml`, tfYaml(NODE_ID));
writeIfMissing(`tf/blocks/${NODE_ID}/rulebook.yml`, rulebookYml(NODE_ID));
writeIfMissing(`tf/blocks/${NODE_ID}/validate.tf`, validateTf());

writeIfMissing("tools/tf-lang-cli/index.mjs", cliIndex());
writeIfMissing("tools/tf-lang-cli/expand.mjs", cliExpand());
writeIfMissing("tools/tf-checker/scan-diff.mjs", scanDiff());

writeIfMissing("scripts/probe-lsp-diag.mjs", probeDiag());
writeIfMissing("scripts/probe-lsp-hover.mjs", probeHover());
writeIfMissing("scripts/probe-lsp-codeaction.mjs", probeAction());

writeIfMissing(".github/workflows/checkpoint.yml", workflow());

if (!NO_VSCODE) {
  writeIfMissing(".vscode/tasks.json", vscodeTasks(NODE_ID));
}

// chmod executables
for (const p of [
  "tools/tf-lang-cli/index.mjs",
  "tools/tf-checker/scan-diff.mjs",
  "scripts/probe-lsp-diag.mjs",
  "scripts/probe-lsp-hover.mjs",
  "scripts/probe-lsp-codeaction.mjs"
]) {
  try { fs.chmodSync(p, 0o755); } catch { }
}

pkgPatch();

console.log("\nNext:");
console.log(`  1) pnpm add -D yaml picomatch`);
console.log(`  2) node tools/tf-lang-cli/index.mjs open ${NODE_ID}`);
console.log(`  3) git diff -U0 --no-color | node tools/tf-lang-cli/index.mjs run ${NODE_ID} cp1_baseline --diff -`);
