// @tf-test kind=product area=pilot speed=medium deps=node
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';

import { describe, expect, it, vi } from 'vitest';
import { Frame, Order, canonFrame, seedRng, validateOrder } from '@tf-lang/pilot-core';
import { STRATEGY_DEFAULTS, createStrategy, runStrategy, writeOrdersNdjson } from '../src/index.js';
import { runCli } from '../src/cli.js';

function sampleFrames(): Frame[] {
  return [
    canonFrame({ ts: 1, sym: 'BTCUSDT', seq: 0, bid: '100', ask: '101', last: '100.5', volume: '1' }),
    canonFrame({ ts: 2, sym: 'BTCUSDT', seq: 1, bid: '100.2', ask: '101.2', last: '100.7', volume: '1' }),
    canonFrame({ ts: 3, sym: 'BTCUSDT', seq: 2, bid: '100.4', ask: '101.4', last: '100.9', volume: '1' }),
    canonFrame({ ts: 4, sym: 'BTCUSDT', seq: 3, bid: '100.6', ask: '101.6', last: '101.1', volume: '1' }),
    canonFrame({ ts: 5, sym: 'BTCUSDT', seq: 4, bid: '100.3', ask: '101.3', last: '100.4', volume: '1' }),
    canonFrame({ ts: 6, sym: 'BTCUSDT', seq: 5, bid: '100.1', ask: '101.1', last: '100.0', volume: '1' }),
    canonFrame({ ts: 7, sym: 'BTCUSDT', seq: 6, bid: '99.9', ask: '100.9', last: '99.6', volume: '1' }),
    canonFrame({ ts: 8, sym: 'BTCUSDT', seq: 7, bid: '100.0', ask: '101.0', last: '100.2', volume: '1' })
  ];
}

describe('pilot-strategy', () => {
  it('exposes centralised defaults', () => {
    expect(STRATEGY_DEFAULTS.momentum.window).toBeGreaterThan(0);
    expect(STRATEGY_DEFAULTS.meanReversion.delta).toBeGreaterThan(0);
  });

  it('momentum strategy emits breakout orders deterministically', () => {
    const strategy = createStrategy('momentum', { seed: 42 });
    const frames = sampleFrames();
    const state = { seed: 42, cash: '0', positions: {} };
    const orders = frames.flatMap((frame) => strategy.decide(state, frame));
    expect(orders.length).toBeGreaterThan(0);
    for (const order of orders) {
      expect(validateOrder(order)).toBe(true);
      expect(order.id.startsWith('momentum-')).toBe(true);
    }
  });

  it('mean reversion strategy emits buys when price is below band', () => {
    const frames = sampleFrames();
    const { orders } = runStrategy({ strategy: 'meanReversion', framesPath: '', seed: 7 }, frames);
    const sides = new Set(orders.map((order) => order.side));
    expect(sides.has('buy')).toBe(true);
    expect(sides.has('sell')).toBe(false);
  });

  it('applies configuration overrides', () => {
    const frames = sampleFrames();
    const { orders } = runStrategy(
      { strategy: 'momentum', framesPath: '', seed: 3, params: { quantity: '2' } },
      frames,
    );
    for (const order of orders) {
      expect(order.quantity).toBe('2');
    }
  });

  it('uses strategy-specific rng offsets', () => {
    const frames = sampleFrames();
    const { orders } = runStrategy({ strategy: 'meanReversion', framesPath: '', seed: 5 }, frames);
    expect(orders.length).toBeGreaterThan(0);
    const rng = seedRng(5 + STRATEGY_DEFAULTS.meanReversion.rngOffset);
    const expectedFirst = rng();
    const firstOrder = orders[0];
    expect(firstOrder.meta?.rng).toBeCloseTo(expectedFirst, 12);
  });

  it('writes identical orders NDJSON given the same seed', () => {
    const frames = sampleFrames();
    const base = mkdtempSync(join(tmpdir(), 'pilot-strategy-ndjson-'));
    const outA = join(base, 'orders-a.ndjson');
    const outB = join(base, 'orders-b.ndjson');
    const options = { strategy: 'momentum' as const, framesPath: '', seed: 42 };
    writeOrdersNdjson(outA, runStrategy(options, frames).orders);
    writeOrdersNdjson(outB, runStrategy(options, frames).orders);
    const first = readFileSync(outA, 'utf-8');
    const second = readFileSync(outB, 'utf-8');
    expect(second).toBe(first);
    rmSync(base, { recursive: true, force: true });
  });

  it('rejects invalid orders when writing NDJSON', () => {
    const base = mkdtempSync(join(tmpdir(), 'pilot-strategy-invalid-'));
    const outPath = join(base, 'orders.ndjson');
    const invalidOrder = {
      id: 'o-1',
      ts: 1,
      sym: '',
      side: 'buy',
      quantity: '1',
    } as Order;
    expect(() => writeOrdersNdjson(outPath, [invalidOrder])).toThrow(/Order validation failed/);
    rmSync(base, { recursive: true, force: true });
  });

  it('cli refuses to overwrite outputs without --force', () => {
    const base = mkdtempSync(join(tmpdir(), 'pilot-strategy-cli-'));
    const framesPath = join(base, 'frames.ndjson');
    const outPath = join(base, 'orders.ndjson');
    const frames = sampleFrames();
    writeFileSync(framesPath, frames.map((frame) => JSON.stringify(frame)).join('\n') + '\n');
    writeFileSync(outPath, 'existing');
    const errorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
    const code = runCli([
      'run',
      '--strategy',
      'momentum',
      '--frames',
      framesPath,
      '--seed',
      '42',
      '--out',
      outPath,
    ]);
    expect(code).toBe(1);
    errorSpy.mockRestore();
    rmSync(base, { recursive: true, force: true });
  });
});
