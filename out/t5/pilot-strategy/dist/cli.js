"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const fs_1 = __importDefault(require("fs"));
const path_1 = __importDefault(require("path"));
const readline_1 = __importDefault(require("readline"));
const index_1 = require("../../pilot-core/dist/index");
const strategies = {
    momentum: momentumStrategy,
    meanReversion: meanReversionStrategy
};
function momentumStrategy(runtime, frame) {
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
    const orders = [];
    if (price > priorHigh) {
        orders.push(createOrder(runtime, frame, 'buy', frame.ask, '0.001'));
    }
    else if (price < priorLow) {
        orders.push(createOrder(runtime, frame, 'sell', frame.bid, '0.001'));
    }
    return orders;
}
function meanReversionStrategy(runtime, frame) {
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
    const orders = [];
    if (price > avg + delta) {
        orders.push(createOrder(runtime, frame, 'sell', frame.bid, '0.0015'));
    }
    else if (price < avg - delta) {
        orders.push(createOrder(runtime, frame, 'buy', frame.ask, '0.0015'));
    }
    return orders;
}
function createOrder(runtime, frame, side, price, qty) {
    const id = `${frame.sym}-${frame.ts}-${runtime.orderSeq}`;
    runtime.orderSeq += 1;
    const order = {
        id,
        ts: frame.ts,
        sym: frame.sym,
        side,
        type: 'limit',
        price: (0, index_1.canonNumber)(price),
        qty: (0, index_1.canonNumber)(qty),
        meta: {
            seed: runtime.core.seed,
            strategy: side === 'buy' ? 'long' : 'short'
        }
    };
    (0, index_1.validateOrder)(order);
    return order;
}
function parseArgs(argv) {
    const args = {
        strategy: 'momentum',
        frames: '',
        seed: 0,
        out: ''
    };
    for (let i = 0; i < argv.length; i += 1) {
        const arg = argv[i];
        if (arg === '--strategy') {
            args.strategy = argv[++i] ?? 'momentum';
        }
        else if (arg === '--frames') {
            args.frames = argv[++i] ?? '';
        }
        else if (arg === '--seed') {
            args.seed = Number.parseInt(argv[++i] ?? '0', 10);
        }
        else if (arg === '--out') {
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
async function readFrames(filePath) {
    const frames = [];
    const stream = fs_1.default.createReadStream(filePath, { encoding: 'utf8' });
    const rl = readline_1.default.createInterface({ input: stream, crlfDelay: Infinity });
    for await (const line of rl) {
        const trimmed = line.trim();
        if (!trimmed)
            continue;
        const parsed = JSON.parse(trimmed);
        (0, index_1.validateFrame)(parsed);
        frames.push(parsed);
    }
    return frames;
}
async function main(argv) {
    const args = parseArgs(argv);
    const frames = await readFrames(path_1.default.resolve(args.frames));
    const rng = (0, index_1.seedRng)(args.seed);
    const runtime = {
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
        orderSeq: Math.floor(rng() * 1000000),
        rng
    };
    const strategyFn = strategies[args.strategy];
    const orders = [];
    frames.forEach((frame) => {
        orders.push(...strategyFn(runtime, frame));
    });
    fs_1.default.mkdirSync(path_1.default.dirname(args.out), { recursive: true });
    const outStream = fs_1.default.createWriteStream(args.out, { encoding: 'utf8' });
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
