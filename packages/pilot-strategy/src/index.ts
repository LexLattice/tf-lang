import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname } from 'node:path';

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

export interface MomentumParameters {
  window: number;
  quantity: string;
  rngOffset: number;
}

export interface MeanReversionParameters {
  window: number;
  delta: number;
  quantity: string;
  rngOffset: number;
}

export type StrategyParameters = {
  momentum: MomentumParameters;
  meanReversion: MeanReversionParameters;
};

export const STRATEGY_DEFAULTS: StrategyParameters = {
  momentum: { window: 3, quantity: '1', rngOffset: 0 },
  meanReversion: { window: 5, delta: 0.15, quantity: '0.5', rngOffset: 1 },
};

export interface StrategyConfig<Name extends StrategyName = StrategyName> {
  seed: number;
  parameters?: Partial<StrategyParameters[Name]>;
}

export interface StrategyRunOptions<Name extends StrategyName = StrategyName> {
  strategy: Name;
  framesPath: string;
  seed: number;
  parameters?: Partial<StrategyParameters[Name]>;
}

export interface StrategyRunResult {
  orders: Order[];
}

export function createStrategy<Name extends StrategyName>(name: Name, config: StrategyConfig<Name>): StrategyContext {
  switch (name) {
    case 'momentum':
      return createMomentumStrategy(config as StrategyConfig<'momentum'>);
    case 'meanReversion':
      return createMeanReversionStrategy(config as StrategyConfig<'meanReversion'>);
    default:
      throw new Error(`Unknown strategy: ${name satisfies never}`);
  }
}

function resolveMomentumParameters(config: StrategyConfig<'momentum'>): MomentumParameters {
  const merged: MomentumParameters = {
    ...STRATEGY_DEFAULTS.momentum,
    ...(config.parameters ?? {}),
  } as MomentumParameters;
  if (!Number.isInteger(merged.window) || merged.window <= 0) {
    throw new Error('Momentum window must be a positive integer');
  }
  return {
    window: merged.window,
    quantity: canonNumber(merged.quantity),
    rngOffset: merged.rngOffset,
  };
}

function createMomentumStrategy(config: StrategyConfig<'momentum'>): StrategyContext {
  const params = resolveMomentumParameters(config);
  const history: number[] = [];
  let counter = 0;
  const rng = seedRng(config.seed + params.rngOffset);
  return {
    decide(_state: State, frame: Frame): Order[] {
      history.push(Number(frame.last));
      if (history.length <= params.window) {
        return [];
      }
      const recent = history.slice(-params.window - 1, -1);
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
          quantity: params.quantity,
          price: frame.ask,
          meta: { trigger: 'breakout', rng: rng() },
        });
      } else if (last < minRecent) {
        orders.push({
          id: `momentum-${counter++}`,
          ts: frame.ts,
          sym: frame.sym,
          side: 'sell',
          quantity: params.quantity,
          price: frame.bid,
          meta: { trigger: 'breakdown', rng: rng() },
        });
      }
      return orders.map(canonOrder);
    },
  };
}

function resolveMeanReversionParameters(config: StrategyConfig<'meanReversion'>): MeanReversionParameters {
  const merged: MeanReversionParameters = {
    ...STRATEGY_DEFAULTS.meanReversion,
    ...(config.parameters ?? {}),
  } as MeanReversionParameters;
  if (!Number.isInteger(merged.window) || merged.window <= 0) {
    throw new Error('Mean reversion window must be a positive integer');
  }
  if (!Number.isFinite(merged.delta) || merged.delta < 0) {
    throw new Error('Mean reversion delta must be a non-negative finite number');
  }
  return {
    window: merged.window,
    delta: merged.delta,
    quantity: canonNumber(merged.quantity),
    rngOffset: merged.rngOffset,
  };
}

function createMeanReversionStrategy(config: StrategyConfig<'meanReversion'>): StrategyContext {
  const params = resolveMeanReversionParameters(config);
  const history: number[] = [];
  let counter = 0;
  const rng = seedRng(config.seed + params.rngOffset);
  return {
    decide(_state: State, frame: Frame): Order[] {
      history.push(Number(frame.last));
      if (history.length < params.window) {
        return [];
      }
      const recent = history.slice(-params.window);
      const avg = recent.reduce((sum, value) => sum + value, 0) / recent.length;
      const last = history[history.length - 1];
      const orders: OrderLike[] = [];
      if (last < avg - params.delta) {
        orders.push({
          id: `meanReversion-${counter++}`,
          ts: frame.ts,
          sym: frame.sym,
          side: 'buy',
          quantity: params.quantity,
          price: frame.bid,
          meta: { trigger: 'below-band', avg, rng: rng() },
        });
      } else if (last > avg + params.delta) {
        orders.push({
          id: `meanReversion-${counter++}`,
          ts: frame.ts,
          sym: frame.sym,
          side: 'sell',
          quantity: params.quantity,
          price: frame.ask,
          meta: { trigger: 'above-band', avg, rng: rng() },
        });
      }
      return orders.map(canonOrder);
    },
  };
}

export function runStrategy<Name extends StrategyName>(options: StrategyRunOptions<Name>, frames: Frame[]): StrategyRunResult {
  const strategy = createStrategy(options.strategy, {
    seed: options.seed,
    parameters: options.parameters,
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
