import fs from "fs-extra";
import path from "node:path";
import { canonNumber, Frame, Order, seedRng, StrategyState, validateOrder } from "@tf-lang/pilot-core";

export type StrategyName = "momentum" | "meanReversion";

export interface Strategy {
  decide(state: StrategyState, frame: Frame): Order[];
}

const LOOKBACK_MOMENTUM = 3;
const MA_WINDOW = 5;
const MA_DELTA = 0.01; // percent threshold

interface StrategyRegistryEntry {
  factory(seed: number): Strategy;
}

const strategyRegistry: Record<StrategyName, StrategyRegistryEntry> = {
  momentum: {
    factory: (seed: number) => createMomentumStrategy(seed),
  },
  meanReversion: {
    factory: (seed: number) => createMeanReversionStrategy(seed),
  },
};

function createMomentumStrategy(seed: number): Strategy {
  const rng = seedRng(seed);
  const history: number[] = [];
  return {
    decide(state, frame) {
      history.push(Number(frame.last));
      if (history.length > LOOKBACK_MOMENTUM) {
        history.shift();
      }
      const orders: Order[] = [];
      if (history.length === LOOKBACK_MOMENTUM) {
        const max = Math.max(...history);
        if (Number(frame.last) >= max) {
          const size = canonNumber(rng() > 0.5 ? 2 : 1);
          orders.push(
            validateOrder({
              ts: frame.ts,
              sym: frame.sym,
              id: `${frame.ts}-${frame.seq}-mom`,
              side: "buy",
              type: "market",
              price: frame.ask,
              size,
              meta: { strategy: "momentum" },
            })
          );
          state.positions[frame.sym] = size;
        }
      }
      return orders;
    },
  };
}

function createMeanReversionStrategy(seed: number): Strategy {
  const rng = seedRng(seed ^ 0x9e3779b9);
  const window: number[] = [];
  return {
    decide(state, frame) {
      window.push(Number(frame.last));
      if (window.length > MA_WINDOW) {
        window.shift();
      }
      const orders: Order[] = [];
      if (window.length === MA_WINDOW) {
        const avg = window.reduce((acc, v) => acc + v, 0) / window.length;
        const delta = (MA_DELTA / 100) * avg;
        if (Number(frame.last) > avg + delta) {
          const size = canonNumber(rng() > 0.5 ? -1 : -2);
          orders.push(
            validateOrder({
              ts: frame.ts,
              sym: frame.sym,
              id: `${frame.ts}-${frame.seq}-mr-sell`,
              side: "sell",
              type: "limit",
              price: frame.bid,
              size,
              meta: { strategy: "meanReversion", signal: "above" },
            })
          );
          state.positions[frame.sym] = size;
        } else if (Number(frame.last) < avg - delta) {
          const size = canonNumber(rng() > 0.5 ? 1 : 2);
          orders.push(
            validateOrder({
              ts: frame.ts,
              sym: frame.sym,
              id: `${frame.ts}-${frame.seq}-mr-buy`,
              side: "buy",
              type: "limit",
              price: frame.ask,
              size,
              meta: { strategy: "meanReversion", signal: "below" },
            })
          );
          state.positions[frame.sym] = size;
        }
      }
      return orders;
    },
  };
}

export interface RunOptions {
  strategy: StrategyName;
  framesPath: string;
  seed: number;
  out?: string;
}

export async function loadFrames(framesPath: string): Promise<Frame[]> {
  const content = await fs.readFile(framesPath, "utf8");
  const lines = content.split("\n").map((line) => line.trim()).filter(Boolean);
  return lines.map((line, index) => {
    try {
      const parsed = JSON.parse(line) as Frame;
      return parsed;
    } catch (error) {
      throw new Error(`Failed to parse frame at line ${index + 1}: ${error}`);
    }
  });
}

export async function runStrategy(options: RunOptions): Promise<Order[]> {
  const entry = strategyRegistry[options.strategy];
  if (!entry) {
    throw new Error(`Unknown strategy: ${options.strategy}`);
  }
  const frames = await loadFrames(path.resolve(options.framesPath));
  const strategy = entry.factory(options.seed);
  const state: StrategyState = {
    seed: options.seed,
    positions: {},
    meta: { strategy: options.strategy },
  };
  const orders: Order[] = [];
  for (const frame of frames) {
    const decided = strategy.decide(state, frame);
    for (const order of decided) {
      orders.push(order);
    }
  }
  if (options.out) {
    await fs.ensureDir(path.dirname(options.out));
    const ndjson = orders.map((order) => JSON.stringify(order)).join("\n");
    await fs.writeFile(options.out, ndjson + (orders.length > 0 ? "\n" : ""), "utf8");
  }
  return orders;
}

export function listStrategies(): StrategyName[] {
  return Object.keys(strategyRegistry) as StrategyName[];
}
