export type DecimalString = string;
export interface Frame {
    ts: number;
    sym: string;
    seq: number;
    bid: DecimalString;
    ask: DecimalString;
    last: DecimalString;
    volume: DecimalString;
}
export interface Order {
    id: string;
    ts: number;
    sym: string;
    side: 'buy' | 'sell';
    type: 'market' | 'limit';
    price: DecimalString;
    qty: DecimalString;
    meta?: Record<string, string | number | boolean | null>;
}
export interface State {
    seed: number;
    positions: Record<string, DecimalString>;
    balances: Record<string, DecimalString>;
    meta?: Record<string, unknown>;
}
export type FrameInput = Omit<Frame, 'bid' | 'ask' | 'last' | 'volume'> & {
    bid: DecimalLike;
    ask: DecimalLike;
    last: DecimalLike;
    volume: DecimalLike;
};
export type DecimalLike = string | number | bigint;
export declare function validateFrame(value: unknown): asserts value is Frame;
export declare function validateOrder(value: unknown): asserts value is Order;
export declare function validateState(value: unknown): asserts value is State;
export declare function canonNumber(value: DecimalLike): DecimalString;
export declare function canonFrame(frame: FrameInput): Frame;
export declare function toMinorUnits(value: DecimalLike, decimals: number): bigint;
export declare function seedRng(seed: number): () => number;
export declare const schemas: {
    frame: {
        $schema: string;
        $id: string;
        title: string;
        type: string;
        additionalProperties: boolean;
        properties: {
            ts: {
                type: string;
                minimum: number;
            };
            sym: {
                type: string;
                minLength: number;
            };
            seq: {
                type: string;
                minimum: number;
            };
            bid: {
                $ref: string;
            };
            ask: {
                $ref: string;
            };
            last: {
                $ref: string;
            };
            volume: {
                $ref: string;
            };
        };
        required: string[];
        definitions: {
            decimal: {
                type: string;
                pattern: string;
            };
        };
    };
    order: {
        $schema: string;
        $id: string;
        title: string;
        type: string;
        additionalProperties: boolean;
        properties: {
            id: {
                type: string;
                minLength: number;
            };
            ts: {
                type: string;
                minimum: number;
            };
            sym: {
                type: string;
                minLength: number;
            };
            side: {
                enum: string[];
            };
            type: {
                enum: string[];
            };
            price: {
                $ref: string;
            };
            qty: {
                $ref: string;
            };
            meta: {
                type: string;
                additionalProperties: {
                    anyOf: {
                        type: string;
                    }[];
                };
            };
        };
        required: string[];
        definitions: {
            decimal: {
                type: string;
                pattern: string;
            };
        };
    };
    state: {
        $schema: string;
        $id: string;
        title: string;
        type: string;
        additionalProperties: boolean;
        properties: {
            seed: {
                type: string;
            };
            positions: {
                type: string;
                additionalProperties: {
                    $ref: string;
                };
            };
            balances: {
                type: string;
                additionalProperties: {
                    $ref: string;
                };
            };
            meta: {
                type: string;
                additionalProperties: boolean;
            };
        };
        required: string[];
        definitions: {
            decimal: {
                type: string;
                pattern: string;
            };
        };
    };
};
