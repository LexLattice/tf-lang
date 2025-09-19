import { defineConfig } from 'vitest/config';
import { fileURLToPath } from 'node:url';

const pilotCore = fileURLToPath(new URL('../pilot-core/src/index.ts', import.meta.url));

export default defineConfig({
  test: {
    environment: 'node',
  },
  resolve: {
    alias: {
      '@tf-lang/pilot-core': pilotCore,
    },
  },
});
