import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';

import { describe, expect, it } from 'vitest';
import { canonFrame, canonOrder } from '@tf-lang/pilot-core';
import {
  evaluateExposureMetrics,
  readFramesNdjson,
  readOrdersNdjson,
  writeEvaluationsNdjson,
} from '../src/index.js';

describe('pilot-risk exposure evaluation', () => {
  it('computes per-symbol exposure metrics', () => {
    const frames = [
      canonFrame({ ts: 1, sym: 'BTCUSDT', seq: 0, bid: '100', ask: '101', last: '100.5', volume: '1' }),
      canonFrame({ ts: 2, sym: 'BTCUSDT', seq: 1, bid: '100', ask: '101', last: '100.0', volume: '1' }),
      canonFrame({ ts: 3, sym: 'BTCUSDT', seq: 2, bid: '99', ask: '100', last: '99.5', volume: '1' }),
      canonFrame({ ts: 4, sym: 'BTCUSDT', seq: 3, bid: '98', ask: '99', last: '98', volume: '1' }),
    ];
    const orders = [
      canonOrder({ id: 'o-1', ts: 1, sym: 'BTCUSDT', side: 'buy', quantity: '1', price: '101' }),
      canonOrder({ id: 'o-2', ts: 2, sym: 'BTCUSDT', side: 'sell', quantity: '0.4', price: '100' }),
      canonOrder({ id: 'o-3', ts: 3, sym: 'BTCUSDT', side: 'sell', quantity: '0.6', price: '99' }),
      canonOrder({ id: 'o-4', ts: 4, sym: 'BTCUSDT', side: 'buy', quantity: '0.2' }),
    ];
    const metrics = evaluateExposureMetrics(orders, frames);
    expect(metrics).toEqual([
      {
        sym: 'BTCUSDT',
        grossNotional: '220',
        netQty: '0.2',
        maxAbsExposure: '101',
        orders: 4,
      },
    ]);
  });

  it('reads and writes ndjson deterministically', () => {
    const base = mkdtempSync(join(tmpdir(), 'pilot-risk-'));
    const ordersPath = join(base, 'orders.ndjson');
    const framesPath = join(base, 'frames.ndjson');
    const evalPath = join(base, 'eval.ndjson');
    const orders = [
      canonOrder({ id: 'o-1', ts: 1, sym: 'ETHUSDT', side: 'buy', quantity: '1', price: '2000' }),
    ];
    const frames = [
      canonFrame({ ts: 1, sym: 'ETHUSDT', seq: 0, bid: '1999', ask: '2001', last: '2000', volume: '5' }),
    ];
    writeFileSync(ordersPath, orders.map((order) => JSON.stringify(order)).join('\n') + '\n');
    writeFileSync(framesPath, frames.map((frame) => JSON.stringify(frame)).join('\n') + '\n');
    const readOrders = readOrdersNdjson(ordersPath);
    const readFrames = readFramesNdjson(framesPath);
    const metrics = evaluateExposureMetrics(readOrders, readFrames);
    writeEvaluationsNdjson(evalPath, metrics);
    const written = readFileSync(evalPath, 'utf-8').trim();
    expect(written).toBe(JSON.stringify(metrics[0]));
    rmSync(base, { recursive: true, force: true });
  });
});
