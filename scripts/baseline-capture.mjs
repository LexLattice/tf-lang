#!/usr/bin/env node
import { copyFile, mkdir } from 'node:fs/promises';
await mkdir('contracts/baseline', { recursive: true });
await copyFile('packages/tf-l0-spec/spec/ids.json','contracts/baseline/ids.json');
await copyFile('packages/tf-l0-spec/spec/catalog.json','contracts/baseline/catalog.json');
console.log('Captured baseline contracts to contracts/baseline/.');
