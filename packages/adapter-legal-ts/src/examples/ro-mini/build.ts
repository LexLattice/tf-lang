
import fs from 'fs';
import path from 'path';
import { buildClaims, legalPrecedence, Query } from '../../legal.js';
import { conflictDetect } from 'claims-core-ts';

const here = path.dirname(new URL(import.meta.url).pathname);
const acts = JSON.parse(fs.readFileSync(path.join(here, 'acts.json'), 'utf-8'));
const clauses = JSON.parse(fs.readFileSync(path.join(here, 'clauses.json'), 'utf-8'));

const datasetVersion = 'ro-mini-2025-09-09';
const claims = buildClaims(clauses, datasetVersion);

const at = '2025-09-09';
const forbiddenRO = Query.count(claims, { kind: 'DEONTIC', modality: 'FORBIDDEN', scope: { jurisdiction: 'RO' }, at });
const forbiddenBuc = Query.count(claims, { kind: 'DEONTIC', modality: 'FORBIDDEN', scope: { jurisdiction: 'RO/Bucuresti' }, at });
const forbiddenS1 = Query.count(claims, { kind: 'DEONTIC', modality: 'FORBIDDEN', scope: { jurisdiction: 'RO/Bucuresti/S1' }, at });

console.log('FORBIDDEN counts @', at);
console.log({ 'RO': forbiddenRO.n, 'RO/Bucuresti': forbiddenBuc.n, 'RO/Bucuresti/S1': forbiddenS1.n });

// Detect unresolved contradictions
const conflicts = conflictDetect(claims, { policy: 'legal', now: at }, legalPrecedence);
console.log('Unresolved contradictions:', conflicts);

// Show sample evidence for FORBIDDEN (RO)
const sampleIds = forbiddenRO.samples;
const samples = claims.filter(c => sampleIds.includes(c.id));
console.log('Samples:', samples.map(s => ({ id: s.id, text: s.evidence[0].source_uri, status: s.status })));
