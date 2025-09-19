import { describe, expect, it } from 'vitest';
import { CompareReport } from '@tf-lang/tf-plan-compare-core';
import { renderHtml, renderMarkdown } from '../src/index.js';

const maliciousReport: CompareReport = {
  version: '0.1.0',
  meta: {
    seed: 99,
    specHash: 'spec-with-xss',
    planVersion: '0.1.0',
    generatedAt: '1970-01-01T00:00:00.000Z',
    notes: ["<script>alert('note')</script>"],
  },
  branches: [
    {
      nodeId: 'branch-1',
      branchName: "<script>alert('branch')</script>",
      planChoice: 'choice',
      rank: 1,
      score: { total: 7.5, risk: 2.5, complexity: 4, perf: 5, devTime: 6, depsReady: 8 },
      summary: "summary <img src=x onerror=alert('summary')>",
      oracles: [
        {
          name: "sec<oracle>",
          status: 'fail',
          details: "<b>broken</b>",
          artifact: 'javascript:alert(1)',
        },
      ],
    },
  ],
};

describe('compare renderer xss hardening', () => {
  it('escapes malicious HTML in markdown output', () => {
    const markdown = renderMarkdown(maliciousReport);
    expect(markdown).not.toContain('<script>');
    expect(markdown).toContain("\\<script\\>alert('branch')\\</script\\>");
    expect(markdown).toContain("summary \\<img src=x onerror=alert('summary')\\>");
    expect(markdown).toContain("- \\<script\\>alert('note')\\</script\\>");
  });

  it('escapes malicious HTML in html output', () => {
    const html = renderHtml(maliciousReport);
    expect(html).toContain('&lt;script&gt;alert(&#39;branch&#39;)&lt;/script&gt;');
    expect(html).not.toMatch(/href=\"javascript:/i);
    expect(html).not.toMatch(/src=\"javascript:/i);
    const expectedHtml = [
      '<!doctype html><html lang="en"><head><meta charset="utf-8" /><meta http-equiv="Content-Security-Policy" content="default-src \'none\'; style-src \'self\' \'unsafe-inline\'; img-src \'self\' data:; connect-src \'none\'; font-src \'none\'; frame-src \'none\'; form-action \'none\'; base-uri \'none\';" /><title>tf-plan comparison</title><style>',
      '  body { font-family: system-ui, sans-serif; margin: 0 auto; max-width: 960px; padding: 1.5rem; background: #f9fafb; color: #111827; }',
      '  h1 { margin-bottom: 1rem; font-size: 1.75rem; }',
      '  p.meta { margin: 0.25rem 0; }',
      '  table { border-collapse: collapse; width: 100%; margin: 1.5rem 0; background: #ffffff; box-shadow: 0 1px 2px rgba(15, 23, 42, 0.1); }',
      '  th, td { border: 1px solid #e5e7eb; padding: 0.5rem 0.75rem; text-align: left; vertical-align: top; }',
      '  th { background: #f3f4f6; font-weight: 600; }',
      '  section { background: #ffffff; padding: 1rem; margin-bottom: 1rem; border: 1px solid #e5e7eb; border-radius: 0.5rem; box-shadow: 0 1px 2px rgba(15, 23, 42, 0.05); }',
      '  section h3 { margin-top: 0; }',
      '  ul { padding-left: 1.25rem; }',
      '  .notes { margin: 0.5rem 0 1rem 0; padding-left: 1.25rem; }',
      '  .notes li { list-style: disc; }',
      '</style></head><body><h1>tf-plan comparison (version 0.1.0)</h1><p class="meta"><strong>Seed:</strong> 99</p><p class="meta"><strong>Spec hash:</strong> spec-with-xss</p><p class="meta"><strong>Plan version:</strong> 0.1.0</p><p class="meta"><strong>Generated at:</strong> 1970-01-01T00:00:00.000Z</p><ul class="notes"><li>&lt;script&gt;alert(&#39;note&#39;)&lt;/script&gt;</li></ul><table><thead><tr><th>Rank</th><th>Branch</th><th>Total</th><th>Risk</th><th>Summary</th></tr></thead><tbody><tr><td>1</td><td>&lt;script&gt;alert(&#39;branch&#39;)&lt;/script&gt;</td><td>7.50</td><td>2.50</td><td>summary &lt;img src=x onerror=alert(&#39;summary&#39;)&gt;</td></tr></tbody></table><section><h3>&lt;script&gt;alert(&#39;branch&#39;)&lt;/script&gt;</h3><ul><li><strong>sec&lt;oracle&gt;</strong>: fail · &lt;b&gt;broken&lt;/b&gt; · artifact: javascript:alert(1)</li></ul></section></body></html>',
    ].join('\n');
    expect(html).toBe(expectedHtml);
  });
});
