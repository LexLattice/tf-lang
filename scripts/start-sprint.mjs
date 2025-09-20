#!/usr/bin/env node
/**
 * Sprint bootstrap helper (4-track).
 * Usage: node scripts/start-sprint.mjs A2
 * Creates local branches: A2/track-1..4 and prints next commands.
 */
const sprint = process.argv[2];
if (!sprint) { console.error('Usage: node scripts/start-sprint.mjs <SPRINT_ID>'); process.exit(2); }
const tracks = [1,2,3,4].map(n=>`${sprint}/track-${n}`);
console.log(`# Run the following to start a 4-lane sprint for ${sprint}:`);
for (const t of tracks) console.log(`git checkout -b ${t} && git push -u origin ${t}`);
console.log(`# After each track finalizes, run 'npm run judge' on each and pick the winner.`);
