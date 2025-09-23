#!/usr/bin/env node
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
  if(expect.jsonpath_eq){ try{ const j=JSON.parse(res.stdout||"{}"); const k=Object.keys(expect.jsonpath_eq)[0]; const key=k.replace(/^\$\./,""); const want=expect.jsonpath_eq[k]; return { ok: JSON.stringify(j[key])===JSON.stringify(want) }; } catch{} }
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
      if(!ch.ok) console.error(`[FAIL] ${r.id} — ${r.command}`);
    }
    const report = { contract_id: `${node}@0.45`, node_id: node, checkpoint: cp, timestamp: new Date().toISOString(), results, evidence };
    fs.mkdirSync("out",{recursive:true}); fs.writeFileSync("out/TFREPORT.json", JSON.stringify(report, null, 2));
    const ok = Object.values(results).every(v => v.ok);
    console.log(`\nRESULT: ${ok ? "GREEN" : "RED"}  (${Object.keys(results).length} probes)`); process.exit(ok?0:3);
  }
  if(!["open","run"].includes(cmd)){
    console.log("usage: tf-lang <open|run> ..."); process.exit(2);
  }
})().catch(e=>{ console.error(e); process.exit(99); });
