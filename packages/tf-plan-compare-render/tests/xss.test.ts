import { describe, expect, it } from 'vitest';
import type { CompareReport } from '@tf-lang/tf-plan-compare-core';
import { renderHtml, renderMarkdown } from '../src/index.js';

const maliciousReport: CompareReport = {
  version: '0.1.0',
  meta: {
    seed: 42,
    specHash: 'badseed',
    planVersion: '0.1.0',
    generatedAt: '1970-01-01T00:00:00.000Z',
    notes: [],
  },
  branches: [
    {
      nodeId: 'evil-node',
      branchName: '<script>alert(1)</script>',
      planChoice: 'choice',
      rank: 1,
      score: { total: 9, risk: 2, complexity: 4, perf: 6, devTime: 5, depsReady: 7 },
      summary: 'Summary <img src=x onerror=alert(2)>',
      oracles: [
        {
          name: 'oracle<script>',
          status: 'pass',
          details: 'detail <b>raw</b>',
          artifact: 'javascript:alert(3)',
        },
      ],
    },
  ],
};

describe('compare renderer sanitisation', () => {
  it('escapes html in markdown output', () => {
    const markdown = renderMarkdown(maliciousReport);
    expect(markdown).not.toContain('<script>');
    expect(markdown).toContain('&lt;script&gt;');
    expect(markdown).not.toContain('javascript:alert');
  });

  it('escapes html in html output', () => {
    const html = renderHtml(maliciousReport);
    expect(html).not.toContain('<script>');
    expect(html).toContain('&lt;script&gt;');
    expect(html).not.toContain('javascript:alert');
    expect(html).toContain('&lt;b&gt;raw&lt;/b&gt;');
    expect(html).not.toContain('<b>raw</b>');
  });
});
