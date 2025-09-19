import { describe, expect, it } from "vitest";
import { evaluate, riskConfigSchema } from "../src/index.js";
import type { Order } from "@tf-lang/pilot-core";

const sampleOrder: Order = {
  ts: 1,
  sym: "BTCUSDT",
  id: "order-1",
  side: "buy",
  type: "market",
  price: "100.00",
  size: "1",
};

describe("pilot-risk evaluate", () => {
  it("passes through validated orders", () => {
    const config = riskConfigSchema.parse({});
    const result = evaluate(config, { seed: 1, positions: {} }, [sampleOrder], {});
    expect(result).toHaveLength(1);
    expect(result[0].id).toBe("order-1");
  });

  it("rejects malformed orders", () => {
    const config = riskConfigSchema.parse({});
    expect(() =>
      evaluate(
        config,
        { seed: 1, positions: {} },
        [{ ...sampleOrder, price: "abc" } as unknown as Order],
        {}
      )
    ).toThrow();
  });
});
