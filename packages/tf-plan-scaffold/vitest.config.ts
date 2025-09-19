import { defineConfig } from 'vitest/config';
import { resolve } from 'node:path';

export default defineConfig({
  test: {
    alias: {
      '@tf-lang/tf-plan-core': resolve(__dirname, '../tf-plan-core/src/index.ts'),
      '@tf-lang/tf-plan-scaffold-core': resolve(__dirname, '../tf-plan-scaffold-core/src/index.ts'),
      '@tf-lang/tf-plan-enum': resolve(__dirname, '../tf-plan-enum/src/index.ts'),
    },
  },
});
