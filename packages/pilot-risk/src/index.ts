import Ajv, { ValidateFunction } from 'ajv';
import { Frame, Order, State } from '@tf-lang/pilot-core';
import configSchema from './schemas/config.schema.json' with { type: 'json' };

export interface RiskConfig {
  mode: 'passThrough';
  meta?: Record<string, unknown>;
}

export interface RiskContext {
  evaluate(state: State, orders: Order[], frame: Frame): Order[];
}

const ajv = new Ajv({ allErrors: true, strict: false });
const validateConfig: ValidateFunction<RiskConfig> = ajv.compile<RiskConfig>(configSchema as any);

export function createRisk(config: unknown): RiskContext {
  if (!validateConfig(config)) {
    throw new Error(ajv.errorsText(validateConfig.errors));
  }
  return {
    evaluate(_state: State, orders: Order[], _frame: Frame): Order[] {
      return orders;
    },
  };
}

export { configSchema, validateConfig };
