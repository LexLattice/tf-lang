"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const assert_1 = __importDefault(require("assert"));
const index_1 = require("../../pilot-core/dist/index");
const index_2 = require("./index");
const baseState = {
    seed: 42,
    positions: {},
    balances: {},
    meta: {}
};
const frame = (0, index_1.canonFrame)({
    ts: 1700000000000,
    sym: 'BTCUSDT',
    seq: 0,
    bid: '34450.10',
    ask: '34450.20',
    last: '34450.15',
    volume: '1.0'
});
const orders = [
    {
        id: 'BTCUSDT-1',
        ts: frame.ts,
        sym: frame.sym,
        side: 'buy',
        type: 'limit',
        price: (0, index_1.canonNumber)('34450.10'),
        qty: (0, index_1.canonNumber)('0.1')
    }
];
const config = { maxOrdersPerTick: 1 };
const evaluated = (0, index_2.evaluate)(baseState, orders, frame, config);
assert_1.default.strictEqual(evaluated.length, 1);
assert_1.default.deepStrictEqual(evaluated, orders);
let threw = false;
try {
    (0, index_2.evaluate)(baseState, orders, frame, { maxOrdersPerTick: -1 });
}
catch (error) {
    threw = true;
}
assert_1.default.ok(threw, 'evaluate should throw on invalid config');
