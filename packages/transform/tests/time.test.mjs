import assert from 'node:assert/strict';
import { runTransform } from '../index.mjs';

const parsed = runTransform({ op: 'time.parseTimestamp' }, { value: '2024-05-01T12:34:56Z' });
assert.equal(parsed.iso, '2024-05-01T12:34:56.000Z');
assert.equal(typeof parsed.epoch_ms, 'number');

const aligned = runTransform({ op: 'time.align', unit: 'hour' }, { timestamp: parsed.epoch_ms + 15 * 60 * 1000 });
assert.equal(aligned.iso, '2024-05-01T12:00:00.000Z');
assert.equal(aligned.interval_ms, 60 * 60 * 1000);

const window = runTransform({ op: 'time.windowKey', unit: 'hour' }, { timestamp: parsed.epoch_ms });
assert.equal(window.key, '2024-05-01T12:00:00.000Z/2024-05-01T13:00:00.000Z');
assert.equal(window.interval_ms, 60 * 60 * 1000);
assert.equal(window.start_ms, aligned.epoch_ms);
assert.equal(window.end_ms, aligned.epoch_ms + aligned.interval_ms);

console.log('time transforms OK');
