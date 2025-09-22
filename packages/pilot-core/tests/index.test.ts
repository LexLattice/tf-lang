// @tf-test kind=product area=pilot speed=fast deps=node
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';

import { describe, expect, it } from 'vitest';
import {
  assertValidFrame,
  assertValidOrder,
  assertValidState,
  canonFrame,
  canonNumber,
  canonOrder,
  seedRng,
  summariseFile,
  writeStatusFile,
  toMinorUnits,
  parseCommonFlags,
} from '../src/index.js';

describe('pilot-core helpers', () => {
  it('canonicalises frames and validates', () => {
    const frame = canonFrame({
      ts: 1000,
      sym: 'BTCUSDT',
      seq: 1,
      bid: '0100.500',
      ask: 100.6,
      last: '100.55',
      volume: '0001.000',
    });
    expect(frame.bid).toBe('100.5');
    expect(frame.volume).toBe('1');
    expect(() => assertValidFrame(frame)).not.toThrow();
  });

  it('canonicalises orders', () => {
    const order = canonOrder({
      id: 'o-1',
      ts: 2000,
      sym: 'BTCUSDT',
      side: 'buy',
      quantity: '001.000',
      price: 100.5,
    });
    expect(order.quantity).toBe('1');
    expect(order.price).toBe('100.5');
    expect(() => assertValidOrder(order)).not.toThrow();
  });

  it('validates state', () => {
    expect(() =>
      assertValidState({
        seed: 42,
        cash: '1000',
        positions: {},
      }),
    ).not.toThrow();
  });

  it('produces deterministic rng output', () => {
    const rng = seedRng(42);
    expect(rng()).toBeCloseTo(0.44829055899754167, 12);
    const rng2 = seedRng('seed');
    expect(rng2()).toBeCloseTo(0.02951375348493457, 12);
  });

  it('canonicalises numbers', () => {
    expect(canonNumber('010.5000')).toBe('10.5');
    expect(canonNumber(0.1)).toBe('0.1');
  });

  it('converts to minor units respecting scale', () => {
    expect(toMinorUnits('10.5', 2)).toBe('1050');
    expect(toMinorUnits('0.005', 3)).toBe('5');
    expect(() => toMinorUnits('1.234', 2)).toThrow();
  });

  it('summarises files and writes status payloads', () => {
    const base = mkdtempSync(join(tmpdir(), 'pilot-core-status-'));
    const ndjsonPath = join(base, 'sample.ndjson');
    writeFileSync(ndjsonPath, '{"a":1}\n{"b":2}\n');
    const summary = summariseFile(ndjsonPath);
    expect(summary.lines).toBe(2);
    expect(summary.sha256).toMatch(/^[0-9a-f]{64}$/);
    const statusPath = join(base, 'status.json');
    writeStatusFile({
      seed: 42,
      slice: '0:1:1',
      files: { sample: { path: ndjsonPath } },
      outPath: statusPath,
    });
    const status = JSON.parse(readFileSync(statusPath, 'utf-8'));
    expect(status.ok).toBe(true);
    expect(status.seed).toBe(42);
    expect(status.files.sample.lines).toBe(2);
    rmSync(base, { recursive: true, force: true });
  });

  it('parses common CLI flags and enforces output safety', () => {
    const base = mkdtempSync(join(tmpdir(), 'pilot-core-flags-'));
    const outPath = join(base, 'frames.ndjson');
    const result = parseCommonFlags(['--seed', '42', '--slice', '0:10:1', '--out', outPath], {
      requireOut: true,
    });
    expect(result.seed).toBe(42);
    expect(result.slice).toBe('0:10:1');
    expect(result.outPath).toBe(outPath);
    expect(result.rest).toHaveLength(0);
    writeFileSync(outPath, 'existing');
    expect(() =>
      parseCommonFlags(['--seed', '42', '--out', outPath], {
        requireOut: true,
      }),
    ).toThrow(/already exists/);
    rmSync(base, { recursive: true, force: true });

    const statusPath = resolve('out/t5/status.json');
    if (existsSync(statusPath)) {
      const payload = JSON.parse(readFileSync(statusPath, 'utf-8'));
      expect(payload.ok).toBe(true);
      expect(payload.seed).toBe(42);
      expect(payload.slice).toBe('0:50:1');
    }
  });
});
