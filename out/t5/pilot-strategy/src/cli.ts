import fs from 'fs';
import path from 'path';
import readline from 'readline';
import {
  Frame,
  Order,
  State,
  canonNumber,
  seedRng,
  validateFrame,
  validateOrder
} from '../../pilot-core/dist/index';

type StrategyName = 'momentum' | 'meanReversion';

interface StrategyRuntime {
  core: State;
  memory: {
    momentum: number[];
    meanReversion: number[];
  };
  orderSeq: number;
  rng: () => number;
}

type StrategyFn = (runtime: StrategyRuntime, frame: Frame) => Order[];

const strategies: Record<StrategyName, StrategyFn> = {
  momentum: momentumStrategy,
  meanReversion: meanReversionStrategy
};

function momentumStrategy(runtime: StrategyRuntime, frame: Frame): Order[] {
  const closes = runtime.memory.momentum;
  const price = Number(frame.last);
  closes.push(price);
  if (closes.length > 5) {
    closes.shift();
  }

  if (closes.length < 3) {
    return [];
  }

  const recent = closes.slice(-3);
  const priorHigh = Math.max(...recent.slice(0, 2));
  const priorLow = Math.min(...recent.slice(0, 2));
  const orders: Order[] = [];

  if (price > priorHigh) {
    orders.push(createOrder(runtime, frame, 'buy', frame.ask, '0.001'));
  } else if (price < priorLow) {
    orders.push(createOrder(runtime, frame, 'sell', frame.bid, '0.001'));
  }

  return orders;
}

function meanReversionStrategy(runtime: StrategyRuntime, frame: Frame): Order[] {
  const closes = runtime.memory.meanReversion;
  const price = Number(frame.last);
  closes.push(price);
  if (closes.length > 10) {
    closes.shift();
  }

  const window = 5;
  if (closes.length < window) {
    return [];
  }

  const recent = closes.slice(-window);
  const avg = recent.reduce((acc, value) => acc + value, 0) / recent.length;
  const delta = 0.5;
  const orders: Order[] = [];

  if (price > avg + delta) {
    orders.push(createOrder(runtime, frame, 'sell', frame.bid, '0.0015'));
  } else if (price < avg - delta) {
    orders.push(createOrder(runtime, frame, 'buy', frame.ask, '0.0015'));
  }

  return orders;
}

function createOrder(runtime: StrategyRuntime, frame: Frame, side: 'buy' | 'sell', price: string, qty: string): Order {
  const id = `${frame.sym}-${frame.ts}-${runtime.orderSeq}`;
  runtime.orderSeq += 1;
  const order: Order = {
    id,
    ts: frame.ts,
    sym: frame.sym,
    side,
    type: 'limit',
    price: canonNumber(price),
    qty: canonNumber(qty),
    meta: {
      seed: runtime.core.seed,
      strategy: side === 'buy' ? 'long' : 'short'
    }
  };
  validateOrder(order);
  return order;
}

interface StrategyArgs {
  strategy: StrategyName;
  frames: string;
  seed: number;
  out: string;
}

function parseArgs(argv: string[]): StrategyArgs {
  const args: StrategyArgs = {
    strategy: 'momentum',
    frames: '',
    seed: 0,
    out: ''
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--strategy') {
      args.strategy = (argv[++i] as StrategyName) ?? 'momentum';
    } else if (arg === '--frames') {
      args.frames = argv[++i] ?? '';
    } else if (arg === '--seed') {
      args.seed = Number.parseInt(argv[++i] ?? '0', 10);
    } else if (arg === '--out') {
      args.out = argv[++i] ?? '';
    }
  }

  if (!args.frames || !args.out) {
    throw new Error('Usage: pilot-strategy run --strategy <name> --frames <file> --seed <n> --out <file>');
  }

  if (!['momentum', 'meanReversion'].includes(args.strategy)) {
    throw new Error(`Unknown strategy: ${args.strategy}`);
  }

  return args;
}

async function readFrames(filePath: string): Promise<Frame[]> {
  const frames: Frame[] = [];
  const stream = fs.createReadStream(filePath, { encoding: 'utf8' });
  const rl = readline.createInterface({ input: stream, crlfDelay: Infinity });
  for await (const line of rl) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    const parsed = JSON.parse(trimmed);
    validateFrame(parsed);
    frames.push(parsed);
  }
  return frames;
}

async function main(argv: string[]): Promise<void> {
  const args = parseArgs(argv);
  const frames = await readFrames(path.resolve(args.frames));
  const rng = seedRng(args.seed);
  const runtime: StrategyRuntime = {
    core: {
      seed: args.seed,
      positions: {},
      balances: {},
      meta: { strategy: args.strategy }
    },
    memory: {
      momentum: [],
      meanReversion: []
    },
    orderSeq: Math.floor(rng() * 1_000_000),
    rng
  };

  const strategyFn = strategies[args.strategy];
  const orders: Order[] = [];
  frames.forEach((frame) => {
    orders.push(...strategyFn(runtime, frame));
  });

  fs.mkdirSync(path.dirname(args.out), { recursive: true });
  const outStream = fs.createWriteStream(args.out, { encoding: 'utf8' });
  orders.forEach((order) => {
    outStream.write(`${JSON.stringify(order)}\n`);
  });
  outStream.end();
}

if (require.main === module) {
  main(process.argv.slice(2)).catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
