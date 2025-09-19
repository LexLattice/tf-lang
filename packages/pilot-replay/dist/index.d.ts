import { Frame } from '@tf-lang/pilot-core';
export interface SliceSpec {
    start?: number;
    end?: number;
    step?: number;
}
export interface ReplayOptions {
    input: string;
    seed?: number | string;
    slice?: SliceSpec;
}
export interface ReplayResult {
    frames: Frame[];
    meta: {
        seed?: number | string;
        input: string;
        slice?: SliceSpec;
    };
}
export declare function readCsv(path: string): Promise<string>;
export interface TickRow {
    ts: string;
    sym: string;
    bid?: string;
    ask?: string;
    last?: string;
    vol?: string;
    [key: string]: string | undefined;
}
export declare function parseCsv(content: string): TickRow[];
export declare function buildFrames(rows: TickRow[]): Frame[];
export declare function replay(options: ReplayOptions): Promise<ReplayResult>;
export declare function writeNdjson(path: string, frames: Frame[]): Promise<void>;
export declare function parseSlice(value: string | undefined): SliceSpec | undefined;
