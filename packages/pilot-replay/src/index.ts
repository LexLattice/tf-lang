import fs from "fs-extra";
import { parse } from "csv-parse";
import { canonFrame, Frame } from "@tf-lang/pilot-core";

export interface SliceSpec {
  start: number;
  end?: number;
  step: number;
}

export interface ReplayOptions {
  input: string;
  seed: number;
  slice?: SliceSpec;
}

export async function readCsvFrames(inputPath: string): Promise<Frame[]> {
  const content = await fs.readFile(inputPath, "utf8");
  const frames: Frame[] = [];
  await new Promise<void>((resolve, reject) => {
    const parser = parse(content, {
      columns: true,
      trim: true,
      skip_empty_lines: true,
    });
    let index = 0;
    parser.on("readable", () => {
      let record: Record<string, string> | null;
      // eslint-disable-next-line no-cond-assign
      while ((record = parser.read()) !== null) {
        const ts = Number(record.ts);
        const sym = record.sym;
        if (!sym) {
          reject(new Error(`Missing symbol at row ${index}`));
          return;
        }
        if (!Number.isFinite(ts)) {
          reject(new Error(`Invalid timestamp at row ${index}`));
          return;
        }
        const frame = canonFrame({
          ts,
          sym,
          seq: record.seq ? Number(record.seq) : index,
          bid: record.bid,
          ask: record.ask,
          last: record.last,
          volume: record.volume ?? "0",
        });
        frames.push(frame);
        index += 1;
      }
    });
    parser.on("error", reject);
    parser.on("end", () => resolve());
  });
  return frames.sort((a, b) => {
    if (a.ts !== b.ts) return a.ts - b.ts;
    const symCmp = a.sym.localeCompare(b.sym);
    if (symCmp !== 0) return symCmp;
    return a.seq - b.seq;
  });
}

export function sliceFrames(frames: Frame[], slice?: SliceSpec): Frame[] {
  if (!slice) return frames;
  const { start, end, step } = slice;
  const effectiveEnd = end ?? frames.length;
  const output: Frame[] = [];
  for (let i = start; i < Math.min(effectiveEnd, frames.length); i += step) {
    if (i >= 0) {
      output.push(frames[i]);
    }
  }
  return output;
}

export async function replay(options: ReplayOptions): Promise<Frame[]> {
  const frames = await readCsvFrames(options.input);
  return sliceFrames(frames, options.slice);
}
