#!/usr/bin/env node
/**
 * Winner merge helper (prints commands).
 * Usage: node scripts/pick-winner.mjs A2 track-3
 * Merges A2/track-3 into phase staging branch: phase-A/staging
 */
const sprint = process.argv[2];
const track = process.argv[3];
if (!sprint || !track) { console.error('Usage: node scripts/pick-winner.mjs <SPRINT_ID> <track-N>'); process.exit(2); }
const src = `${sprint}/${track}`.replace(/\/+/, '/');
const staging = `phase-${sprint[0]}/staging`;
console.log(`# Winner merge commands:`);
console.log(`git checkout ${staging} || git checkout -b ${staging}`);
console.log(`git merge --no-ff ${src}`);
console.log(`git push origin ${staging}`);
