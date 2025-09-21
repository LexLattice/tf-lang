#!/usr/bin/env node
const BASE_MS = 1700000000000;
const STEP_NS = 1_000_000n; // 1ms
const BASE_NS = BigInt(BASE_MS) * 1_000_000n;

let state = { counter: -STEP_NS };

function createClock() {
  return {
    nowNs() {
      state.counter += STEP_NS;
      return BASE_NS + state.counter;
    },
    reset() {
      state.counter = -STEP_NS;
    },
    get __tf_pilot() {
      return true;
    }
  };
}

export function installDeterministicClock() {
  state.counter = -STEP_NS;
  const clock = createClock();
  globalThis.__tf_clock = clock;
  return clock;
}

export function resetDeterministicClock() {
  const clock = globalThis.__tf_clock;
  if (clock && clock.__tf_pilot && typeof clock.reset === 'function') {
    clock.reset();
    return;
  }
  installDeterministicClock();
}

if (!globalThis.__tf_clock || !globalThis.__tf_clock.__tf_pilot) {
  installDeterministicClock();
}
