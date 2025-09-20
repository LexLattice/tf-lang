#!/usr/bin/env node
import { createHash } from 'node:crypto';
import { readdir, readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';
const ROOTS=['out/0.4']; const OUT_DIR='out/0.4';
async function* walk(base, rel=""){ const dir=path.join(base,rel); const entries=await readdir(dir,{withFileTypes:true}).catch(()=>[]); for(const e of entries){ const p=path.join(rel,e.name); if(e.isDirectory()) yield* walk(base,p); else if(e.isFile()) yield path.join(base,p);}}
const sha256 = (buf)=>'sha256:'+createHash('sha256').update(buf).digest('hex');
await mkdir(OUT_DIR,{recursive:true});
const files=[]; for(const r of ROOTS) for await (const f of walk(r)) files.push(f); files.sort();
const lines=[], items=[]; for(const f of files){ const h=sha256(await readFile(f)); lines.push(`${h}  ${f}`); items.push({path:f, sha256:h}); }
const manifestSha=sha256(Buffer.from(lines.join('\n'),'utf8'));
await writeFile(path.join(OUT_DIR,'digests.txt'),lines.join('\n')+'\n','utf8');
await writeFile(path.join(OUT_DIR,'digests.json'),JSON.stringify({files:items,manifest_sha256:manifestSha},null,2)+'\n','utf8');
console.log(`Wrote ${items.length} digests. manifest=${manifestSha}`);
