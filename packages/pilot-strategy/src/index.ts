import { readFileSync, writeFileSync } from 'node:fs';
import { dirname } from 'node:path';
import { mkdirSync } from 'node:fs';

import {
  Frame,
  Order,
  OrderLike,
  State,
  canonNumber,
  canonOrder,
  seedRng,
} from '@tf-lang/pilot-core';

export type StrategyName = 'momentum' | 'meanReversion';

export interface StrategyContext {
  decide(state: State, frame: Frame): Order[];
}

export const StrategyDefaults = {
  momentum: {
    breakoutWindow: 3,
    quantity: canonNumber('1'),
  },
  meanReversion: {
    window: 5,
    delta: canonNumber('0.15'),
    quantity: canonNumber('0.5'),
  },
} as const;

export interface StrategyConfig {
  seed: number;
}

export interface StrategyRunOptions {
  strategy: StrategyName;
  framesPath: string;
  seed: number;
}

export interface StrategyRunResult {
  orders: Order[];
}

export function createStrategy(name: StrategyName, config: StrategyConfig): StrategyContext {
  switch (name) {
    case 'momentum':
      return createMomentumStrategy(config);
    case 'meanReversion':
      return createMeanReversionStrategy(config);
    default:
      throw new Error(`Unknown strategy: ${name satisfies never}`);
  }
}

function createMomentumStrategy(config: StrategyConfig): StrategyContext {
  const { breakoutWindow, quantity } = StrategyDefaults.momentum;
  const history: number[] = [];
  let counter = 0;
  const rng = seedRng(config.seed);
  return {
    decide(_state: State, frame: Frame): Order[] {
      history.push(Number(frame.last));
      if (history.length <= breakoutWindow) {
        return [];
      }
      const recent = history.slice(-breakoutWindow - 1, -1);
      const last = history[history.length - 1];
      const maxRecent = Math.max(...recent);
      const minRecent = Math.min(...recent);
      const orders: OrderLike[] = [];
      if (last > maxRecent) {
        orders.push({
          id: `momentum-${counter++}`,
          ts: frame.ts,
          sym: frame.sym,
          side: 'buy',
          quantity,
          price: frame.ask,
          meta: { trigger: 'breakout', rng: rng() },
        });
      } else if (last < minRecent) {
        orders.push({
          id: `momentum-${counter++}`,
          ts: frame.ts,
          sym: frame.sym,
          side: 'sell',
          quantity,
          price: frame.bid,
          meta: { trigger: 'breakdown', rng: rng() },
        });
      }
      return orders.map(canonOrder);
    },
  };
}

function createMeanReversionStrategy(config: StrategyConfig): StrategyContext {
  const { window, delta, quantity } = StrategyDefaults.meanReversion;
  const deltaValue = Number(delta);
  const history: number[] = [];
  let counter = 0;
  const rng = seedRng(config.seed + 1);
  return {
    decide(_state: State, frame: Frame): Order[] {
      history.push(Number(frame.last));
      if (history.length < window) {
        return [];
      }
      const recent = history.slice(-window);
      const avg = recent.reduce((sum, value) => sum + value, 0) / recent.length;
      const last = history[history.length - 1];
      const orders: OrderLike[] = [];
      if (last < avg - deltaValue) {
        orders.push({
          id: `meanReversion-${counter++}`,
          ts: frame.ts,
          sym: frame.sym,
          side: 'buy',
          quantity,
          price: frame.bid,
          meta: { trigger: 'below-band', avg, rng: rng() },
        });
      } else if (last > avg + deltaValue) {
        orders.push({
          id: `meanReversion-${counter++}`,
          ts: frame.ts,
          sym: frame.sym,
          side: 'sell',
          quantity,
          price: frame.ask,
          meta: { trigger: 'above-band', avg, rng: rng() },
        });
      }
      return orders.map(canonOrder);
    },
  };
}

export function runStrategy(options: StrategyRunOptions, frames: Frame[]): StrategyRunResult {
  const strategy = createStrategy(options.strategy, { seed: options.seed });
  const state: State = { seed: options.seed, cash: '0', positions: {} };
  const orders: Order[] = [];
  for (const frame of frames) {
    const next = strategy.decide(state, frame);
    for (const order of next) {
      orders.push(order);
    }
  }
  return { orders };
}

export function readFramesNdjson(path: string): Frame[] {
  const content = readFileSync(path, 'utf-8');
  return content
    .split(/\n/)
    .filter((line) => line.trim().length > 0)
    .map((line) => JSON.parse(line) as Frame);
}

export function writeOrdersNdjson(path: string, orders: Order[]): void {
  const directory = dirname(path);
  mkdirSync(directory, { recursive: true });
  const content = orders.map((order) => JSON.stringify(order)).join('\n');
  writeFileSync(path, content + (orders.length ? '\n' : ''));
}
