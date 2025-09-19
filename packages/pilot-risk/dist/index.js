import { z } from 'zod';
import { FrameSchema, OrderSchema, StateSchema } from '@tf-lang/pilot-core';
export const RiskConfigSchema = z
    .object({
    maxOrders: z.number().int().nonnegative().optional(),
    allowShort: z.boolean().optional()
})
    .partial();
export function evaluate(state, orders, frame, config = {}) {
    StateSchema.parse(state);
    FrameSchema.parse(frame);
    orders.forEach((order) => OrderSchema.parse(order));
    const parsed = RiskConfigSchema.parse(config);
    if (parsed.maxOrders !== undefined) {
        return orders.slice(0, parsed.maxOrders);
    }
    return [...orders];
}
