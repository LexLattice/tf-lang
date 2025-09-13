import initSqlJs from 'sql.js';
import { readFileSync } from 'node:fs';
import { createRequire } from 'node:module';

const require = createRequire(import.meta.url);
const wasmPath = require.resolve('sql.js/dist/sql-wasm.wasm');
const wasmBinary = readFileSync(wasmPath);
const schema = readFileSync(new URL('../fixtures/schema.sql', import.meta.url), 'utf8');
const seed = readFileSync(new URL('../fixtures/seed.sql', import.meta.url), 'utf8');
const SQL = await initSqlJs({ wasmBinary });

export function buildDb() {
  const db = new SQL.Database();
  db.run(schema);
  db.run(seed);
  return db;
}
