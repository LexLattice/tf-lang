import { describe, expect, it } from 'vitest';
import { CompareReport } from '@tf-lang/tf-plan-compare-core';
import { renderHtml, renderMarkdown } from '../src/index.js';

const report: CompareReport = {
  version: '0.1.0',
  meta: { seed: 42, planVersion: '0.1.0', specHash: 'deadbeef', generatedAt: '1970-01-01T00:00:00.000Z', notes: [] },
  branches: [
    {
      nodeId: 'node',
      branchName: 't4/demo',
      planChoice: 'choice',
      rank: 1,
      score: { total: 9, risk: 2, complexity: 4, perf: 6, devTime: 5, depsReady: 7 },
      summary: 'top branch',
      oracles: [],
    },
  ],
};

describe('renderers', () => {
  it('renders markdown deterministically', () => {
    const md = renderMarkdown(report);
    expect(md).toContain('# tf-plan comparison');
  });

  it('renders html deterministically', () => {
    const html = renderHtml(report);
    expect(html).toContain('<table');
  });
});
