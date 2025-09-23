#!/usr/bin/env node
import fs from "node:fs"; import * as yaml from "yaml"; import picomatch from "picomatch";
const readStdin = () => new Promise(r => { let d=""; process.stdin.setEncoding("utf8"); process.stdin.on("data",c=>d+=c); process.stdin.on("end",()=>r(d)); });
function globs(ps){ const ms=(ps||[]).map(g=>picomatch(g,{dot:true})); return f=>ms.length===0||ms.some(m=>m(f)); }
function parseDiff(t){ const out=[]; let cur=null,nl=0; const L=t.split("\n");
  for(const line of L){
    if(line.startsWith("+++ ")){ const b=line.replace("+++ b/","").replace("+++ ",""); if(cur) out.push(cur); cur={file:b,added:[]}; continue; }
    if(line.startsWith("@@")){ const m=/@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@/.exec(line); nl=m?parseInt(m[1],10):0; continue; }
    if(!cur) continue;
    if(line.startsWith("+")&&!line.startsWith("+++")){ cur.added.push({ln:nl,text:line.slice(1)}); nl++; }
    else if(line.startsWith(" ")) nl++;
    else if(line.startsWith("diff --git ")){ out.push(cur); cur=null; }
  } if(cur) out.push(cur); out.forEach(f=>f.file=f.file.replace(/^b\//,"")); return out;
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
  const report=scan(files,cfg); process.stdout.write(JSON.stringify(report,null,2)+"\n"); process.exitCode=report.ok?0:2;
})().catch(e=>{ console.error(e); process.exit(99); });
