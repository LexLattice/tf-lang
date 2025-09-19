"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const fs_1 = __importDefault(require("fs"));
const path_1 = __importDefault(require("path"));
const readline_1 = __importDefault(require("readline"));
const index_1 = require("../../pilot-core/dist/index");
function parseArgs(argv) {
    const args = {
        input: '',
        seed: 0,
        slice: null,
        out: ''
    };
    for (let i = 0; i < argv.length; i += 1) {
        const arg = argv[i];
        if (arg === '--input') {
            args.input = argv[++i] ?? '';
        }
        else if (arg === '--seed') {
            args.seed = Number.parseInt(argv[++i] ?? '0', 10);
        }
        else if (arg === '--slice') {
            args.slice = argv[++i] ?? null;
        }
        else if (arg === '--out') {
            args.out = argv[++i] ?? '';
        }
    }
    if (!args.input || !args.out) {
        throw new Error('Usage: pilot-replay replay --input <file> --seed <n> [--slice a:b:c] --out <file>');
    }
    return args;
}
function parseSlice(value) {
    if (!value) {
        return { start: 0, end: null, step: 1 };
    }
    const [startStr, endStr, stepStr] = value.split(':');
    const start = startStr ? Number.parseInt(startStr, 10) : 0;
    const end = endStr ? Number.parseInt(endStr, 10) : null;
    const step = stepStr ? Number.parseInt(stepStr, 10) : 1;
    if (Number.isNaN(start) || (end !== null && Number.isNaN(end)) || Number.isNaN(step) || step <= 0) {
        throw new Error(`Invalid slice spec: ${value}`);
    }
    return { start, end, step };
}
async function loadFrames(filePath) {
    const stream = fs_1.default.createReadStream(filePath);
    const rl = readline_1.default.createInterface({ input: stream, crlfDelay: Infinity });
    const frames = [];
    let header = null;
    const seqBySymbol = new Map();
    for await (const line of rl) {
        const trimmed = line.trim();
        if (!trimmed)
            continue;
        if (!header) {
            header = trimmed.split(',').map((h) => h.trim());
            continue;
        }
        const values = trimmed.split(',').map((v) => v.trim());
        const record = {};
        header.forEach((key, index) => {
            record[key] = values[index] ?? '';
        });
        const sym = record['sym'];
        if (!sym) {
            throw new Error('Missing symbol in CSV row');
        }
        const seq = seqBySymbol.get(sym) ?? 0;
        seqBySymbol.set(sym, seq + 1);
        const frameInput = {
            ts: Number.parseInt(record['ts'], 10),
            sym,
            seq,
            bid: record['bid'],
            ask: record['ask'],
            last: record['last'],
            volume: record['volume']
        };
        frames.push((0, index_1.canonFrame)(frameInput));
    }
    frames.sort((a, b) => {
        if (a.ts !== b.ts)
            return a.ts - b.ts;
        if (a.sym !== b.sym)
            return a.sym.localeCompare(b.sym);
        return a.seq - b.seq;
    });
    return frames;
}
function applySlice(frames, spec) {
    const start = Math.max(spec.start, 0);
    const end = spec.end == null ? frames.length : Math.min(spec.end, frames.length);
    const selected = [];
    for (let i = start; i < end; i += spec.step) {
        const frame = frames[i];
        if (frame) {
            selected.push(frame);
        }
    }
    return selected;
}
async function main(argv) {
    const args = parseArgs(argv);
    const slice = parseSlice(args.slice);
    const frames = await loadFrames(path_1.default.resolve(args.input));
    const sampled = applySlice(frames, slice);
    fs_1.default.mkdirSync(path_1.default.dirname(args.out), { recursive: true });
    const outStream = fs_1.default.createWriteStream(args.out, { encoding: 'utf8' });
    const rng = (0, index_1.seedRng)(args.seed);
    const seqOffset = Math.floor(rng() * 1000000);
    sampled.forEach((frame) => {
        const canonicalFrame = {
            ...frame,
            seq: frame.seq + seqOffset
        };
        outStream.write(`${JSON.stringify(canonicalFrame)}\n`);
    });
    outStream.end();
}
if (require.main === module) {
    main(process.argv.slice(2)).catch((error) => {
        console.error(error);
        process.exitCode = 1;
    });
}
