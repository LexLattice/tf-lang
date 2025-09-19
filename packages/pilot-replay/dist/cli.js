#!/usr/bin/env node
import { existsSync } from 'node:fs';
import { resolve } from 'node:path';
import { parseSlice, replay, writeNdjson } from './index.js';
function printUsage(message) {
    if (message) {
        console.error(message);
    }
    console.error('Usage: pilot-replay replay --input <file> --out <file> [--slice a:b:c] [--seed <value>]');
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
    if (command !== 'replay') {
        printUsage('Expected sub-command "replay"');
        process.exitCode = 1;
        return;
    }
    const input = options.input;
    const out = options.out;
    if (!input || !out) {
        printUsage('Missing required --input or --out');
        process.exitCode = 1;
        return;
    }
    const resolvedInput = resolve(input);
    if (!existsSync(resolvedInput)) {
        printUsage(`Input file not found: ${resolvedInput}`);
        process.exitCode = 1;
        return;
    }
    const slice = parseSlice(options.slice);
    const seed = options.seed ? Number(options.seed) : undefined;
    const result = await replay({ input: resolvedInput, slice, seed });
    await writeNdjson(resolve(out), result.frames);
}
if (import.meta.url === `file://${process.argv[1]}` || import.meta.url === new URL(import.meta.url).href) {
    main().catch((error) => {
        console.error(error instanceof Error ? error.message : error);
        process.exitCode = 1;
    });
}
