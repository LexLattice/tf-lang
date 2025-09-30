#!/usr/bin/env node
import fs from 'node:fs';

const allowed = new Set(['Transform', 'Publish', 'Subscribe', 'Keypair']);

if (process.argv.length < 3) {
  console.error('usage: assert-kernel-only <l0.json>');
  process.exit(2);
}

const doc = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const nodes = Array.isArray(doc.nodes)
  ? doc.nodes
  : (doc.monitors ?? []).flatMap((monitor) => monitor.nodes ?? []);

const bad = nodes.filter((node) => !allowed.has(node.kind));

if (bad.length > 0) {
  console.error('Non-kernel kinds found:', bad.map((node) => `${node.id}:${node.kind}`).join(', '));
  process.exit(1);
}

console.log('Kernel-only OK');
