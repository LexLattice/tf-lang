import { it, expect, vi } from 'vitest';

it('returns 500 when DB init fails', async () => {
  vi.mock('../src/db.js', () => ({
    openDb: () => { throw new Error('fail'); },
    count: vi.fn(),
    list: vi.fn(),
    getClaim: vi.fn(),
  }));
  const { buildApp } = await import('../src/app.js');
  const app = buildApp();
  const res = await app.inject({ method: 'GET', url: '/claims/count' });
  expect(res.statusCode).toBe(500);
  const res2 = await app.inject({ method: 'GET', url: '/health' });
  expect(res2.statusCode).toBe(500);
  vi.resetModules();
});
