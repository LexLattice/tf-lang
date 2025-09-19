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

export interface MomentumParams {
  window: number;
  quantity: string;
  rngOffset: number;
}

export interface MeanReversionParams {
  window: number;
  delta: number;
  quantity: string;
  rngOffset: number;
}

export type StrategyParams = {
  momentum: MomentumParams;
  meanReversion: MeanReversionParams;
};

export const STRATEGY_DEFAULTS: StrategyParams = {
  momentum: { window: 3, quantity: '1', rngOffset: 0 },
  meanReversion: { window: 5, delta: 0.15, quantity: '0.5', rngOffset: 1 },
};

export interface StrategyConfig<T extends StrategyName> {
  seed: number;
  params?: Partial<StrategyParams[T]>;
}

export interface StrategyRunOptions<T extends StrategyName = StrategyName> {
  strategy: T;
  framesPath: string;
  seed: number;
  params?: Partial<StrategyParams[T]>;
}

export interface StrategyRunResult {
  orders: Order[];
}

export function createStrategy<T extends StrategyName>(
  name: T,
  config: StrategyConfig<T>,
): StrategyContext {
  switch (name) {
    case 'momentum':
      return createMomentumStrategy(config as StrategyConfig<'momentum'>);
    case 'meanReversion':
      return createMeanReversionStrategy(config as StrategyConfig<'meanReversion'>);
    default:
      throw new Error(`Unknown strategy: ${name satisfies never}`);
  }
}

function mergeParams<T extends StrategyName>(
  name: T,
  overrides?: Partial<StrategyParams[T]>,
): StrategyParams[T] {
  return { ...STRATEGY_DEFAULTS[name], ...(overrides ?? {}) } as StrategyParams[T];
}

function createMomentumStrategy(config: StrategyConfig<'momentum'>): StrategyContext {
  const params = mergeParams('momentum', config.params);
  const window = params.window;
  const quantity = canonNumber(params.quantity);
  const history: number[] = [];
  let counter = 0;
  const rng = seedRng(config.seed + params.rngOffset);
  return {
    decide(_state: State, frame: Frame): Order[] {
      history.push(Number(frame.last));
      if (history.length <= window) {
        return [];
      }
      const recent = history.slice(-window - 1, -1);
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
          meta: { trigger: 'breakout', window, rng: rng() },
        });
      } else if (last < minRecent) {
        orders.push({
          id: `momentum-${counter++}`,
          ts: frame.ts,
          sym: frame.sym,
          side: 'sell',
          quantity,
          price: frame.bid,
          meta: { trigger: 'breakdown', window, rng: rng() },
        });
      }
      return orders.map(canonOrder);
    },
  };
}

function createMeanReversionStrategy(config: StrategyConfig<'meanReversion'>): StrategyContext {
  const params = mergeParams('meanReversion', config.params);
  const window = params.window;
  const delta = Number(params.delta);
  const quantity = canonNumber(params.quantity);
  const history: number[] = [];
  let counter = 0;
  const rng = seedRng(config.seed + params.rngOffset);
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
      if (last < avg - delta) {
        orders.push({
          id: `meanReversion-${counter++}`,
          ts: frame.ts,
          sym: frame.sym,
          side: 'buy',
          quantity,
          price: frame.bid,
          meta: { trigger: 'below-band', avg, window, delta, rng: rng() },
        });
      } else if (last > avg + delta) {
        orders.push({
          id: `meanReversion-${counter++}`,
          ts: frame.ts,
          sym: frame.sym,
          side: 'sell',
          quantity,
          price: frame.ask,
          meta: { trigger: 'above-band', avg, window, delta, rng: rng() },
        });
      }
      return orders.map(canonOrder);
    },
  };
}

export function runStrategy<T extends StrategyName>(
  options: StrategyRunOptions<T>,
  frames: Frame[],
): StrategyRunResult {
  const strategy = createStrategy(options.strategy, {
    seed: options.seed,
    params: options.params,
  });
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
