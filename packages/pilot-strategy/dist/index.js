import { promises as fs } from 'node:fs';
import { dirname } from 'node:path';
import { FrameSchema, OrderSchema, StateSchema, createIdFactory } from '@tf-lang/pilot-core';
function ensureContext(state) {
    if (!state.context) {
        state.context = {};
    }
    return state.context;
}
const MOMENTUM_LOOKBACK = 4;
const MEAN_LOOKBACK = 6;
const MEAN_DELTA = 0.4;
function getPrice(frame) {
    return frame.last ?? frame.ask ?? frame.bid;
}
function createOrder(context, frame, side) {
    const price = getPrice(frame);
    const order = OrderSchema.parse({
        id: context.nextId(),
        ts: frame.ts,
        sym: frame.sym,
        side,
        type: 'market',
        qty: '1',
        price
    });
    return order;
}
const momentumStrategy = {
    decide(state, frame, context) {
        const priceStr = getPrice(frame);
        if (!priceStr) {
            return [];
        }
        const price = Number(priceStr);
        const ctx = ensureContext(state);
        const bucket = ctx.momentum ?? {};
        ctx.momentum = bucket;
        const symCtx = bucket[frame.sym] ?? { history: [] };
        bucket[frame.sym] = symCtx;
        symCtx.history.push(price);
        if (symCtx.history.length > MOMENTUM_LOOKBACK) {
            symCtx.history.shift();
        }
        if (symCtx.history.length < MOMENTUM_LOOKBACK) {
            return [];
        }
        const previous = symCtx.history.slice(0, -1);
        const current = symCtx.history[symCtx.history.length - 1];
        const prevHigh = Math.max(...previous);
        const prevLow = Math.min(...previous);
        if (current > prevHigh) {
            return [createOrder(context, frame, 'buy')];
        }
        if (current < prevLow) {
            return [createOrder(context, frame, 'sell')];
        }
        return [];
    }
};
const meanReversionStrategy = {
    decide(state, frame, context) {
        const priceStr = getPrice(frame);
        if (!priceStr) {
            return [];
        }
        const price = Number(priceStr);
        const ctx = ensureContext(state);
        const bucket = ctx.meanReversion ?? {};
        ctx.meanReversion = bucket;
        const symCtx = bucket[frame.sym] ?? { history: [] };
        bucket[frame.sym] = symCtx;
        symCtx.history.push(price);
        if (symCtx.history.length > MEAN_LOOKBACK) {
            symCtx.history.shift();
        }
        if (symCtx.history.length < MEAN_LOOKBACK) {
            return [];
        }
        const mean = symCtx.history.reduce((acc, v) => acc + v, 0) / symCtx.history.length;
        if (price > mean + MEAN_DELTA) {
            return [createOrder(context, frame, 'sell')];
        }
        if (price < mean - MEAN_DELTA) {
            return [createOrder(context, frame, 'buy')];
        }
        return [];
    }
};
const implementations = {
    momentum: momentumStrategy,
    meanReversion: meanReversionStrategy
};
export function getStrategy(name) {
    const impl = implementations[name];
    if (!impl) {
        throw new Error(`Unknown strategy: ${name}`);
    }
    return impl;
}
export function runStrategy(options) {
    const strategy = getStrategy(options.strategy);
    const nextId = createIdFactory(options.seed);
    const state = options.initialState
        ? StateSchema.parse(options.initialState)
        : StateSchema.parse({ cash: '0', positions: {}, context: {} });
    const orders = [];
    for (const frame of options.frames) {
        const canonicalFrame = FrameSchema.parse(frame);
        const produced = strategy.decide(state, canonicalFrame, { nextId });
        for (const order of produced) {
            orders.push(OrderSchema.parse(order));
        }
    }
    return { orders, state };
}
export async function readFrames(path) {
    const content = await fs.readFile(path, 'utf8');
    const lines = content
        .split(/\r?\n/)
        .map((line) => line.trim())
        .filter((line) => line.length > 0);
    return lines.map((line) => FrameSchema.parse(JSON.parse(line)));
}
export async function writeOrders(path, orders) {
    const dir = dirname(path);
    await fs.mkdir(dir, { recursive: true });
    const lines = orders.map((order) => JSON.stringify(order));
    await fs.writeFile(path, `${lines.join('\n')}\n`, 'utf8');
}
