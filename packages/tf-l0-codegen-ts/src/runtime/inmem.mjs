import { createInmemAdapters } from '../adapters/inmem.mjs';
import { runtimeFromAdapters } from './run-ir.mjs';

export function createRuntime(options = {}) {
  const instance = createInmemAdapters(options);
  const runtime = runtimeFromAdapters(instance.adapters);
  runtime.state = {
    adapters: instance.adapters,
    getPublished: instance.getPublished,
    getMetrics: instance.getMetrics,
    getStorageSnapshot: instance.getStorageSnapshot,
    reset: instance.reset,
  };
  runtime.reset = instance.reset;
  runtime.getPublished = instance.getPublished;
  runtime.getMetrics = instance.getMetrics;
  runtime.getStorageSnapshot = instance.getStorageSnapshot;
  return runtime;
}

const inmem = createRuntime();

export default inmem;
