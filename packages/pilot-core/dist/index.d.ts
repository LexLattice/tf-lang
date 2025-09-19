import { z } from 'zod';
export declare const FrameSchema: z.ZodObject<{
    ts: z.ZodString;
    sym: z.ZodString;
    seq: z.ZodNumber;
    bid: z.ZodOptional<z.ZodString>;
    ask: z.ZodOptional<z.ZodString>;
    last: z.ZodOptional<z.ZodString>;
    vol: z.ZodOptional<z.ZodString>;
    meta: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodUnknown>>;
}, "strip", z.ZodTypeAny, {
    ts: string;
    sym: string;
    seq: number;
    bid?: string | undefined;
    ask?: string | undefined;
    last?: string | undefined;
    vol?: string | undefined;
    meta?: Record<string, unknown> | undefined;
}, {
    ts: string;
    sym: string;
    seq: number;
    bid?: string | undefined;
    ask?: string | undefined;
    last?: string | undefined;
    vol?: string | undefined;
    meta?: Record<string, unknown> | undefined;
}>;
export type Frame = z.infer<typeof FrameSchema>;
export declare const OrderSchema: z.ZodObject<{
    id: z.ZodString;
    ts: z.ZodString;
    sym: z.ZodString;
    side: z.ZodEnum<["buy", "sell"]>;
    type: z.ZodEnum<["market", "limit"]>;
    qty: z.ZodString;
    price: z.ZodOptional<z.ZodString>;
    meta: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodUnknown>>;
}, "strip", z.ZodTypeAny, {
    ts: string;
    sym: string;
    type: "market" | "limit";
    id: string;
    side: "buy" | "sell";
    qty: string;
    meta?: Record<string, unknown> | undefined;
    price?: string | undefined;
}, {
    ts: string;
    sym: string;
    type: "market" | "limit";
    id: string;
    side: "buy" | "sell";
    qty: string;
    meta?: Record<string, unknown> | undefined;
    price?: string | undefined;
}>;
export type Order = z.infer<typeof OrderSchema>;
export declare const StateSchema: z.ZodObject<{
    cash: z.ZodString;
    positions: z.ZodRecord<z.ZodString, z.ZodObject<{
        qty: z.ZodString;
        avgPrice: z.ZodOptional<z.ZodString>;
        meta: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodUnknown>>;
    }, "strip", z.ZodTypeAny, {
        qty: string;
        meta?: Record<string, unknown> | undefined;
        avgPrice?: string | undefined;
    }, {
        qty: string;
        meta?: Record<string, unknown> | undefined;
        avgPrice?: string | undefined;
    }>>;
    context: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodUnknown>>;
    meta: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodUnknown>>;
}, "strip", z.ZodTypeAny, {
    cash: string;
    positions: Record<string, {
        qty: string;
        meta?: Record<string, unknown> | undefined;
        avgPrice?: string | undefined;
    }>;
    meta?: Record<string, unknown> | undefined;
    context?: Record<string, unknown> | undefined;
}, {
    cash: string;
    positions: Record<string, {
        qty: string;
        meta?: Record<string, unknown> | undefined;
        avgPrice?: string | undefined;
    }>;
    meta?: Record<string, unknown> | undefined;
    context?: Record<string, unknown> | undefined;
}>;
export type State = z.infer<typeof StateSchema>;
export declare const frameJsonSchema: any;
export declare const orderJsonSchema: any;
export declare const stateJsonSchema: any;
export interface FrameInput {
    ts: string | number | bigint;
    sym: string;
    seq: number | bigint;
    bid?: string | number | bigint;
    ask?: string | number | bigint;
    last?: string | number | bigint;
    vol?: string | number | bigint;
    meta?: Record<string, unknown>;
}
export declare function canonNumber(value: string | number | bigint): string;
export declare function toMinorUnits(value: string | number | bigint, scale: number): {
    units: string;
    scale: number;
};
export declare function canonFrame(input: FrameInput): Frame;
export type Rng = () => number;
export declare function seedRng(seed: number | string | bigint): Rng;
export declare function createIdFactory(seed: number | string | bigint): () => string;
export declare const validators: {
    frame: (value: unknown) => {
        ts: string;
        sym: string;
        seq: number;
        bid?: string | undefined;
        ask?: string | undefined;
        last?: string | undefined;
        vol?: string | undefined;
        meta?: Record<string, unknown> | undefined;
    };
    order: (value: unknown) => {
        ts: string;
        sym: string;
        type: "market" | "limit";
        id: string;
        side: "buy" | "sell";
        qty: string;
        meta?: Record<string, unknown> | undefined;
        price?: string | undefined;
    };
    state: (value: unknown) => {
        cash: string;
        positions: Record<string, {
            qty: string;
            meta?: Record<string, unknown> | undefined;
            avgPrice?: string | undefined;
        }>;
        meta?: Record<string, unknown> | undefined;
        context?: Record<string, unknown> | undefined;
    };
};
export type { FrameInput as CanonicalFrameInput };
