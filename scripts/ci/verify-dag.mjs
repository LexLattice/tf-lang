#!/usr/bin/env node
import fs from 'node:fs';

const files = process.argv.slice(2);
if (files.length === 0) {
  console.error('Usage: verify-dag.mjs <pipelines/*.l0.json ...>');
  process.exit(2);
}

function collectVarRefs(value, refs) {
  if (typeof value === 'string') {
    const matches = value.matchAll(/@([A-Za-z0-9_]+)/g);
    for (const match of matches) {
      refs.add(match[1]);
    }
    return;
  }
  if (Array.isArray(value)) {
    value.forEach((entry) => collectVarRefs(entry, refs));
    return;
  }
  if (value && typeof value === 'object') {
    for (const child of Object.values(value)) {
      collectVarRefs(child, refs);
    }
  }
}

let failed = false;

for (const file of files) {
  const data = JSON.parse(fs.readFileSync(file, 'utf8'));
  const nodes = Array.isArray(data.nodes)
    ? data.nodes
    : data.nodes && typeof data.nodes === 'object'
      ? Object.values(data.nodes)
      : [];
  if (nodes.length === 0) {
    console.error(`No nodes found in ${file}`);
    failed = true;
    continue;
  }

  const producerByVar = new Map();
  for (const node of nodes) {
    if (!node || typeof node !== 'object') continue;
    const outputs = node.out;
    if (outputs && typeof outputs === 'object') {
      for (const value of Object.values(outputs)) {
        if (typeof value === 'string' && value.length > 0) {
          producerByVar.set(value, node.id);
        }
      }
    }
  }

  const dependencies = new Map();
  const missingRefs = [];

  for (const node of nodes) {
    if (!node || typeof node !== 'object') continue;
    const refs = new Set();
    collectVarRefs(node.in, refs);
    if (node.filter) collectVarRefs(node.filter, refs);
    if (node.spec) collectVarRefs(node.spec, refs);
    if (node.payload) collectVarRefs(node.payload, refs);
    if (node.metadata) collectVarRefs(node.metadata, refs);

    const deps = new Set();
    for (const ref of refs) {
      const producer = producerByVar.get(ref);
      if (producer && producer !== node.id) {
        deps.add(producer);
      } else if (!producer) {
        missingRefs.push({ node: node.id, ref });
      }
    }
    dependencies.set(node.id, deps);
  }

  if (missingRefs.length > 0) {
    failed = true;
    console.error(`Missing variable references in ${file}:`);
    for (const miss of missingRefs) {
      console.error(` - ${miss.node || '<unknown>'} depends on '${miss.ref}'`);
    }
  }

  // Kahn's algorithm for cycle detection
  const indegree = new Map();
  for (const id of dependencies.keys()) {
    indegree.set(id, 0);
  }
  for (const deps of dependencies.values()) {
    for (const dep of deps) {
      indegree.set(dep, indegree.get(dep) ?? 0);
    }
  }
  for (const [id, deps] of dependencies.entries()) {
    for (const dep of deps) {
      indegree.set(id, (indegree.get(id) ?? 0) + 1);
    }
  }

  const queue = [...IndegreeZero(indegree)];
  const visited = [];
  const indegreeCopy = new Map(indegree);
  while (queue.length > 0) {
    const current = queue.shift();
    visited.push(current);
    for (const [id, deps] of dependencies.entries()) {
      if (deps.has(current)) {
        indegreeCopy.set(id, indegreeCopy.get(id) - 1);
        if (indegreeCopy.get(id) === 0) {
          queue.push(id);
        }
      }
    }
  }

  if (visited.length !== dependencies.size) {
    failed = true;
    console.error(`Cycle detected in ${file} (visited ${visited.length} of ${dependencies.size} nodes)`);
  }
}

if (failed) {
  process.exit(1);
}

function* IndegreeZero(indegree) {
  for (const [id, value] of indegree.entries()) {
    if (value === 0 || value === undefined) {
      yield id;
    }
  }
}
