#!/usr/bin/env node
import { readFile } from 'node:fs/promises';

function parseJSONL(s){ return s.trim().split(/\r?\n/).map(l => { try { return JSON.parse(l); } catch { return {}; } }); }
function take(seq){ return seq.map(x => x.prim_id || x.prim || x.id).filter(Boolean); }

const arg = k => { const i = process.argv.indexOf(k); return i>=0 ? process.argv[i+1] : null; };
const A = await readFile(arg('--a'), 'utf8').catch(()=> '');
const B = await readFile(arg('--b'), 'utf8').catch(()=> '');
const eq = JSON.stringify(take(parseJSONL(A))) === JSON.stringify(take(parseJSONL(B)));
console.log(JSON.stringify({ equal: eq }, null, 2));
process.exit(eq ? 0 : 1);
