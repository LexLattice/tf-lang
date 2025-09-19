import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';
import { defineConfig } from 'vitest/config';

const here = fileURLToPath(new URL('.', import.meta.url));

export default defineConfig({
  test: {
    environment: 'node',
  },
  resolve: {
    alias: {
      '@tf-lang/tf-plan-core': resolve(here, '../tf-plan-core/src/index.ts'),
      '@tf-lang/tf-plan-compare-core': resolve(here, '../tf-plan-compare-core/src/index.ts'),
    },
  },
});
