// @tf-test kind=product area=checker speed=fast deps=node
import { describe, it, expect } from 'vitest';
import { parseFilters } from '../src/filters.js';

describe('trace filters', () => {
  it('filters by tag and region prefix', () => {
    const predicate = parseFilters(['tag=Transport', 'region=/acct/**']);
    expect(predicate({ tag: { kind: 'Transport' }, region: '/acct/bal' })).toBe(true);
    expect(predicate({ tag: { kind: 'Transport' }, region: '/risk' })).toBe(false);
    expect(predicate({ tag: { kind: 'Witness' }, region: '/acct/x' })).toBe(false);
  });
});
