#!/usr/bin/env node
import fs from 'node:fs';

function usage() {
  console.error('usage: monitor-effects <monitors.l0.json>');
  process.exit(2);
}

const EFFECT_LABELS = {
  Publish: 'Outbound',
  Subscribe: 'Inbound',
  Keypair: 'Entropy',
  Transform: 'Pure',
};

function describeEffect(node) {
  const effect = EFFECT_LABELS[node.kind];
  if (!effect) throw new Error(`unsupported kernel kind: ${node.kind}`);
  return effect;
}

function collect(nodes, prefix) {
  const rows = [];
  nodes.forEach((node, idx) => {
    const effect = describeEffect(node);
    rows.push({
      effect,
      label: `${prefix} :: ${node.id} [${node.kind}]`,
    });
  });
  return rows;
}

async function main() {
  const argv = process.argv.slice(2);
  if (argv.length < 1) usage();
  const doc = JSON.parse(fs.readFileSync(argv[0], 'utf8'));
  for (const monitor of doc.monitors ?? []) {
    const rows = collect(monitor.nodes ?? [], monitor.monitor_id ?? 'unknown');
    for (const row of rows) {
      console.log(`${row.effect.padEnd(8)} | ${row.label}`);
    }
  }
}

main().catch((err) => {
  console.error(err?.message ?? err);
  process.exit(1);
});
