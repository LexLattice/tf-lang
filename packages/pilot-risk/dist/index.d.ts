import { z } from 'zod';
import { Frame, Order, State } from '@tf-lang/pilot-core';
export declare const RiskConfigSchema: z.ZodObject<{
    maxOrders: z.ZodOptional<z.ZodOptional<z.ZodNumber>>;
    allowShort: z.ZodOptional<z.ZodOptional<z.ZodBoolean>>;
}, "strip", z.ZodTypeAny, {
    maxOrders?: number | undefined;
    allowShort?: boolean | undefined;
}, {
    maxOrders?: number | undefined;
    allowShort?: boolean | undefined;
}>;
export type RiskConfig = z.infer<typeof RiskConfigSchema>;
export declare function evaluate(state: State, orders: Order[], frame: Frame, config?: RiskConfig): Order[];
