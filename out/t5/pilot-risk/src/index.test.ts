import assert from 'assert';
import { Frame, Order, State, canonFrame, canonNumber } from '../../pilot-core/dist/index';
import { evaluate, RiskConfig } from './index';

const baseState: State = {
  seed: 42,
  positions: {},
  balances: {},
  meta: {}
};

const frame: Frame = canonFrame({
  ts: 1700000000000,
  sym: 'BTCUSDT',
  seq: 0,
  bid: '34450.10',
  ask: '34450.20',
  last: '34450.15',
  volume: '1.0'
});

const orders: Order[] = [
  {
    id: 'BTCUSDT-1',
    ts: frame.ts,
    sym: frame.sym,
    side: 'buy',
    type: 'limit',
    price: canonNumber('34450.10'),
    qty: canonNumber('0.1')
  }
];

const config: RiskConfig = { maxOrdersPerTick: 1 };

const evaluated = evaluate(baseState, orders, frame, config);
assert.strictEqual(evaluated.length, 1);
assert.deepStrictEqual(evaluated, orders);

let threw = false;
try {
  evaluate(baseState, orders, frame, { maxOrdersPerTick: -1 } as RiskConfig);
} catch (error) {
  threw = true;
}
assert.ok(threw, 'evaluate should throw on invalid config');
