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

export interface StrategyOverrideOptions {
  window?: number;
  delta?: number;
  quantity?: string;
}

interface StrategyConfigBase {
  seed: number;
}

interface MomentumResolvedConfig extends StrategyConfigBase {
  breakoutWindow: number;
  quantity: string;
  rngOffset: number;
}

interface MeanReversionResolvedConfig extends StrategyConfigBase {
  lookbackWindow: number;
  delta: number;
  quantity: string;
  rngOffset: number;
}

export const StrategyDefaults = {
  momentum: {
    breakoutWindow: 3,
    quantity: '1',
    rngOffset: 0,
  },
  meanReversion: {
    lookbackWindow: 5,
    delta: 0.15,
    quantity: '0.5',
    rngOffset: 1,
  },
} as const;

export interface StrategyRunOptions {
  strategy: StrategyName;
  framesPath: string;
  seed: number;
  overrides?: StrategyOverrideOptions;
}

export interface StrategyRunResult {
  orders: Order[];
}

export function createStrategy(name: StrategyName, config: StrategyConfigBase & { overrides?: StrategyOverrideOptions }): StrategyContext {
  switch (name) {
    case 'momentum':
      return createMomentumStrategy(resolveMomentumConfig(config.seed, config.overrides));
    case 'meanReversion':
      return createMeanReversionStrategy(resolveMeanReversionConfig(config.seed, config.overrides));
    default:
      throw new Error(`Unknown strategy: ${name satisfies never}`);
  }
}

function resolveMomentumConfig(seed: number, overrides?: StrategyOverrideOptions): MomentumResolvedConfig {
  const defaults = StrategyDefaults.momentum;
  const breakoutWindow = overrides?.window ?? defaults.breakoutWindow;
  if (!Number.isInteger(breakoutWindow) || breakoutWindow <= 0) {
    throw new Error('Momentum breakout window must be a positive integer');
  }
  const quantity = overrides?.quantity ?? defaults.quantity;
  return { seed, breakoutWindow, quantity, rngOffset: defaults.rngOffset };
}

function resolveMeanReversionConfig(seed: number, overrides?: StrategyOverrideOptions): MeanReversionResolvedConfig {
  const defaults = StrategyDefaults.meanReversion;
  const lookbackWindow = overrides?.window ?? defaults.lookbackWindow;
  if (!Number.isInteger(lookbackWindow) || lookbackWindow <= 0) {
    throw new Error('Mean reversion lookback window must be a positive integer');
  }
  const delta = overrides?.delta ?? defaults.delta;
  if (!(typeof delta === 'number' && Number.isFinite(delta) && delta >= 0)) {
    throw new Error('Mean reversion delta must be a non-negative finite number');
  }
  const quantity = overrides?.quantity ?? defaults.quantity;
  return { seed, lookbackWindow, delta, quantity, rngOffset: defaults.rngOffset };
}

function createMomentumStrategy(config: MomentumResolvedConfig): StrategyContext {
  const history: number[] = [];
  let counter = 0;
  const rng = seedRng(config.seed + config.rngOffset);
  return {
    decide(_state: State, frame: Frame): Order[] {
      history.push(Number(frame.last));
      if (history.length <= config.breakoutWindow) {
        return [];
      }
      const recent = history.slice(-config.breakoutWindow - 1, -1);
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
          quantity: canonNumber(config.quantity),
          price: frame.ask,
          meta: { trigger: 'breakout', rng: rng() },
        });
      } else if (last < minRecent) {
        orders.push({
          id: `momentum-${counter++}`,
          ts: frame.ts,
          sym: frame.sym,
          side: 'sell',
          quantity: canonNumber(config.quantity),
          price: frame.bid,
          meta: { trigger: 'breakdown', rng: rng() },
        });
      }
      return orders.map(canonOrder);
    },
  };
}

function createMeanReversionStrategy(config: MeanReversionResolvedConfig): StrategyContext {
  const history: number[] = [];
  let counter = 0;
  const rng = seedRng(config.seed + config.rngOffset);
  return {
    decide(_state: State, frame: Frame): Order[] {
      history.push(Number(frame.last));
      if (history.length < config.lookbackWindow) {
        return [];
      }
      const recent = history.slice(-config.lookbackWindow);
      const avg = recent.reduce((sum, value) => sum + value, 0) / recent.length;
      const last = history[history.length - 1];
      const orders: OrderLike[] = [];
      if (last < avg - config.delta) {
        orders.push({
          id: `meanReversion-${counter++}`,
          ts: frame.ts,
          sym: frame.sym,
          side: 'buy',
          quantity: canonNumber(config.quantity),
          price: frame.bid,
          meta: { trigger: 'below-band', avg, rng: rng() },
        });
      } else if (last > avg + config.delta) {
        orders.push({
          id: `meanReversion-${counter++}`,
          ts: frame.ts,
          sym: frame.sym,
          side: 'sell',
          quantity: canonNumber(config.quantity),
          price: frame.ask,
          meta: { trigger: 'above-band', avg, rng: rng() },
        });
      }
      return orders.map(canonOrder);
    },
  };
}

export function runStrategy(options: StrategyRunOptions, frames: Frame[]): StrategyRunResult {
  const strategyOverrides = options.overrides;
  const strategy = createStrategy(options.strategy, { seed: options.seed, overrides: strategyOverrides });
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
