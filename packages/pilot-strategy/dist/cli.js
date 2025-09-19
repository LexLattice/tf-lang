#!/usr/bin/env node
import { resolve } from 'node:path';
import { OrderSchema } from '@tf-lang/pilot-core';
import { getStrategy, readFrames, runStrategy, writeOrders } from './index.js';
function printUsage(message) {
    if (message) {
        console.error(message);
    }
    console.error('Usage: pilot-strategy run --strategy <momentum|meanReversion> --frames <file> --seed <value> --out <file>');
}
function parseArgs(argv) {
    const args = [...argv];
    const command = args.shift();
    const options = {};
    while (args.length > 0) {
        const token = args.shift();
        if (!token)
            break;
        if (!token.startsWith('--')) {
            continue;
        }
        const key = token.slice(2);
        const value = args[0] && !args[0].startsWith('--') ? args.shift() : 'true';
        options[key] = value;
    }
    return { command, options };
}
export async function main(argv = process.argv.slice(2)) {
    const { command, options } = parseArgs(argv);
    if (command !== 'run') {
        printUsage('Expected sub-command "run"');
        process.exitCode = 1;
        return;
    }
    const name = options.strategy;
    const framesPath = options.frames;
    const seed = options.seed;
    const out = options.out;
    if (!name || !framesPath || !seed || !out) {
        printUsage('Missing required options');
        process.exitCode = 1;
        return;
    }
    const strategy = getStrategy(name);
    const frames = await readFrames(resolve(framesPath));
    const result = runStrategy({
        strategy: name,
        frames,
        seed: Number(seed)
    });
    const canonicalOrders = result.orders.map((order) => OrderSchema.parse(order));
    await writeOrders(resolve(out), canonicalOrders);
}
if (import.meta.url === `file://${process.argv[1]}` || import.meta.url === new URL(import.meta.url).href) {
    main().catch((error) => {
        console.error(error instanceof Error ? error.message : error);
        process.exitCode = 1;
    });
}
