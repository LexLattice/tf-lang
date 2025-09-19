import { z } from 'zod';
import { Frame, FrameSchema, Order, OrderSchema, State, StateSchema } from '@tf-lang/pilot-core';

export const RiskConfigSchema = z
  .object({
    maxOrders: z.number().int().nonnegative().optional(),
    allowShort: z.boolean().optional()
  })
  .partial();

export type RiskConfig = z.infer<typeof RiskConfigSchema>;

export function evaluate(
  state: State,
  orders: Order[],
  frame: Frame,
  config: RiskConfig = {}
): Order[] {
  StateSchema.parse(state);
  FrameSchema.parse(frame);
  orders.forEach((order) => OrderSchema.parse(order));
  const parsed = RiskConfigSchema.parse(config);
  if (parsed.maxOrders !== undefined) {
    return orders.slice(0, parsed.maxOrders);
  }
  return [...orders];
}
