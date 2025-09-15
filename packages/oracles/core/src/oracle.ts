import type { Oracle, OracleCheck } from "./types.js";

const ensureName = (name: string): string => {
  if (name.trim().length === 0) {
    throw new Error("oracle name must not be empty");
  }
  return name;
};

export const defineOracle = <I, O>(
  name: string,
  check: OracleCheck<I, O>,
): Oracle<I, O> => ({
  name: ensureName(name),
  async check(input: I, ctx) {
    return check(input, ctx);
  },
});

