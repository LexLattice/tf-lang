import Ajv from 'ajv';
import addFormats from 'ajv-formats';
import { Frame, Order, State, validateFrame, validateOrder, validateState } from '../../pilot-core/dist/index';

const configSchema = {
  type: 'object',
  additionalProperties: false,
  properties: {
    maxOrdersPerTick: { type: 'integer', minimum: 0 }
  },
  required: ['maxOrdersPerTick']
} as const;

export interface RiskConfig {
  maxOrdersPerTick: number;
}

const ajv = new Ajv({ allErrors: true, strict: false });
addFormats(ajv);
const validateConfig = ajv.compile<RiskConfig>(configSchema);

export function evaluate(
  state: State,
  orders: Order[],
  frame: Frame,
  config: RiskConfig
): Order[] {
  validateState(state);
  validateFrame(frame);
  orders.forEach((order) => validateOrder(order));

  if (!validateConfig(config)) {
    throw new Error(`Invalid risk config: ${ajv.errorsText(validateConfig.errors)}`);
  }

  if (orders.length > config.maxOrdersPerTick) {
    return orders.slice(0, config.maxOrdersPerTick);
  }

  return orders;
}

export const riskSchemas = {
  config: configSchema
};
