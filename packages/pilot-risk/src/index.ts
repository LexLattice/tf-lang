import { Order, StrategyState, validateOrder } from "@tf-lang/pilot-core";
import { z } from "zod";

export const riskConfigSchema = z
  .object({
    maxNotional: z.string().regex(/^-?\d+(?:\.\d+)?$/).default("0"),
  })
  .strict();

export type RiskConfig = z.infer<typeof riskConfigSchema>;

export function evaluate(
  _config: RiskConfig,
  _state: StrategyState,
  orders: Order[],
  _frame: unknown
): Order[] {
  return orders.map((order) => validateOrder(order));
}
