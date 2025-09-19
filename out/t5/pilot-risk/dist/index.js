"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.riskSchemas = void 0;
exports.evaluate = evaluate;
const ajv_1 = __importDefault(require("ajv"));
const ajv_formats_1 = __importDefault(require("ajv-formats"));
const index_1 = require("../../pilot-core/dist/index");
const configSchema = {
    type: 'object',
    additionalProperties: false,
    properties: {
        maxOrdersPerTick: { type: 'integer', minimum: 0 }
    },
    required: ['maxOrdersPerTick']
};
const ajv = new ajv_1.default({ allErrors: true, strict: false });
(0, ajv_formats_1.default)(ajv);
const validateConfig = ajv.compile(configSchema);
function evaluate(state, orders, frame, config) {
    (0, index_1.validateState)(state);
    (0, index_1.validateFrame)(frame);
    orders.forEach((order) => (0, index_1.validateOrder)(order));
    if (!validateConfig(config)) {
        throw new Error(`Invalid risk config: ${ajv.errorsText(validateConfig.errors)}`);
    }
    if (orders.length > config.maxOrdersPerTick) {
        return orders.slice(0, config.maxOrdersPerTick);
    }
    return orders;
}
exports.riskSchemas = {
    config: configSchema
};
