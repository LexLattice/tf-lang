"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.schemas = void 0;
exports.validateFrame = validateFrame;
exports.validateOrder = validateOrder;
exports.validateState = validateState;
exports.canonNumber = canonNumber;
exports.canonFrame = canonFrame;
exports.toMinorUnits = toMinorUnits;
exports.seedRng = seedRng;
const ajv_1 = __importDefault(require("ajv"));
const ajv_formats_1 = __importDefault(require("ajv-formats"));
const frame_schema_json_1 = __importDefault(require("../frame.schema.json"));
const order_schema_json_1 = __importDefault(require("../order.schema.json"));
const state_schema_json_1 = __importDefault(require("../state.schema.json"));
const ajv = new ajv_1.default({ allErrors: true, strict: false, useDefaults: false });
(0, ajv_formats_1.default)(ajv);
function compile(schema) {
    return ajv.compile(schema);
}
const validateFrameFn = compile(frame_schema_json_1.default);
const validateOrderFn = compile(order_schema_json_1.default);
const validateStateFn = compile(state_schema_json_1.default);
function validateFrame(value) {
    if (!validateFrameFn(value)) {
        throw new Error(`Invalid frame: ${ajv.errorsText(validateFrameFn.errors)}`);
    }
}
function validateOrder(value) {
    if (!validateOrderFn(value)) {
        throw new Error(`Invalid order: ${ajv.errorsText(validateOrderFn.errors)}`);
    }
}
function validateState(value) {
    if (!validateStateFn(value)) {
        throw new Error(`Invalid state: ${ajv.errorsText(validateStateFn.errors)}`);
    }
}
function canonNumber(value) {
    let str;
    if (typeof value === 'string') {
        str = value.trim();
    }
    else if (typeof value === 'bigint') {
        str = value.toString();
    }
    else if (Number.isFinite(value)) {
        str = value.toString();
    }
    else {
        throw new Error(`Non-finite number: ${value}`);
    }
    if (!str) {
        return '0';
    }
    const negative = str.startsWith('-');
    if (negative || str.startsWith('+')) {
        str = str.slice(1);
    }
    if (!/^\d*(?:\.\d*)?$/.test(str)) {
        throw new Error(`Invalid decimal value: ${value}`);
    }
    let [intPart, fracPart = ''] = str.split('.');
    intPart = intPart.replace(/^0+(?=\d)/, '');
    fracPart = fracPart.replace(/0+$/, '');
    let normalized = intPart || '0';
    if (fracPart.length > 0) {
        normalized += `.${fracPart}`;
    }
    if (normalized === '0' && negative) {
        return '0';
    }
    return negative ? `-${normalized}` : normalized;
}
function canonFrame(frame) {
    const normalized = {
        ts: typeof frame.ts === 'string' ? Number.parseInt(frame.ts, 10) : frame.ts,
        sym: frame.sym,
        seq: typeof frame.seq === 'string' ? Number.parseInt(frame.seq, 10) : frame.seq,
        bid: canonNumber(frame.bid),
        ask: canonNumber(frame.ask),
        last: canonNumber(frame.last),
        volume: canonNumber(frame.volume)
    };
    validateFrame(normalized);
    return normalized;
}
function toMinorUnits(value, decimals) {
    if (!Number.isInteger(decimals) || decimals < 0) {
        throw new Error(`Invalid decimals: ${decimals}`);
    }
    const canonical = canonNumber(value);
    const negative = canonical.startsWith('-');
    const digits = negative ? canonical.slice(1) : canonical;
    const [intPartRaw, fracPartRaw = ''] = digits.split('.');
    const intPart = intPartRaw || '0';
    if (fracPartRaw.length > decimals) {
        throw new Error(`Too many decimal places: ${canonical} for scale ${decimals}`);
    }
    const fracPart = (fracPartRaw + '0'.repeat(decimals)).slice(0, decimals);
    const scale = BigInt(10) ** BigInt(decimals);
    const base = BigInt(intPart);
    const fraction = fracPart ? BigInt(fracPart) : 0n;
    const total = base * scale + fraction;
    return negative ? -total : total;
}
function seedRng(seed) {
    let state = seed >>> 0;
    return () => {
        state = (state + 0x6d2b79f5) >>> 0;
        let t = state;
        t = Math.imul(t ^ (t >>> 15), t | 1);
        t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
}
exports.schemas = {
    frame: frame_schema_json_1.default,
    order: order_schema_json_1.default,
    state: state_schema_json_1.default
};
