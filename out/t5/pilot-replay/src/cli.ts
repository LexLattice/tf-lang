import fs from 'fs';
import path from 'path';
import readline from 'readline';
import { canonFrame, Frame, FrameInput, seedRng } from '../../pilot-core/dist/index';

interface ReplayArgs {
  input: string;
  seed: number;
  slice: string | null;
  out: string;
}

function parseArgs(argv: string[]): ReplayArgs {
  const args: ReplayArgs = {
    input: '',
    seed: 0,
    slice: null,
    out: ''
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--input') {
      args.input = argv[++i] ?? '';
    } else if (arg === '--seed') {
      args.seed = Number.parseInt(argv[++i] ?? '0', 10);
    } else if (arg === '--slice') {
      args.slice = argv[++i] ?? null;
    } else if (arg === '--out') {
      args.out = argv[++i] ?? '';
    }
  }

  if (!args.input || !args.out) {
    throw new Error('Usage: pilot-replay replay --input <file> --seed <n> [--slice a:b:c] --out <file>');
  }

  return args;
}

interface SliceSpec {
  start: number;
  end: number | null;
  step: number;
}

function parseSlice(value: string | null): SliceSpec {
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

async function loadFrames(filePath: string): Promise<Frame[]> {
  const stream = fs.createReadStream(filePath);
  const rl = readline.createInterface({ input: stream, crlfDelay: Infinity });

  const frames: Frame[] = [];
  let header: string[] | null = null;
  const seqBySymbol = new Map<string, number>();

  for await (const line of rl) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    if (!header) {
      header = trimmed.split(',').map((h) => h.trim());
      continue;
    }

    const values = trimmed.split(',').map((v) => v.trim());
    const record: Record<string, string> = {};
    header.forEach((key, index) => {
      record[key] = values[index] ?? '';
    });

    const sym = record['sym'];
    if (!sym) {
      throw new Error('Missing symbol in CSV row');
    }

    const seq = seqBySymbol.get(sym) ?? 0;
    seqBySymbol.set(sym, seq + 1);

    const frameInput: FrameInput = {
      ts: Number.parseInt(record['ts'], 10),
      sym,
      seq,
      bid: record['bid'],
      ask: record['ask'],
      last: record['last'],
      volume: record['volume']
    };

    frames.push(canonFrame(frameInput));
  }

  frames.sort((a, b) => {
    if (a.ts !== b.ts) return a.ts - b.ts;
    if (a.sym !== b.sym) return a.sym.localeCompare(b.sym);
    return a.seq - b.seq;
  });

  return frames;
}

function applySlice(frames: Frame[], spec: SliceSpec): Frame[] {
  const start = Math.max(spec.start, 0);
  const end = spec.end == null ? frames.length : Math.min(spec.end, frames.length);
  const selected: Frame[] = [];
  for (let i = start; i < end; i += spec.step) {
    const frame = frames[i];
    if (frame) {
      selected.push(frame);
    }
  }
  return selected;
}

async function main(argv: string[]): Promise<void> {
  const args = parseArgs(argv);
  const slice = parseSlice(args.slice);
  const frames = await loadFrames(path.resolve(args.input));
  const sampled = applySlice(frames, slice);

  fs.mkdirSync(path.dirname(args.out), { recursive: true });
  const outStream = fs.createWriteStream(args.out, { encoding: 'utf8' });
  const rng = seedRng(args.seed);
  const seqOffset = Math.floor(rng() * 1_000_000);

  sampled.forEach((frame) => {
    const canonicalFrame: Frame = {
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
