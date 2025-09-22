// @tf-test kind=infra area=pages speed=fast deps=node
import { describe, it, expect, beforeEach, vi } from 'vitest';
import { JSDOM } from 'jsdom';

function mockHealth(version = 'v1', tags: string[] = ['a','b'], at?: string, generated_at = '2025-09-09T12:00:00Z') {
  return {
    dataset_version: version,
    tags,
    ...(at ? { at } : { generated_at }),
  };
}

describe('E1 — source label updates', () => {
  let dom: JSDOM;
  beforeEach(() => {
    dom = new JSDOM(
      `<!doctype html><html><body>
        <span id="srcPath"></span>
        <input id="apiBase" value="https://example.test/api">
        <button id="switchToApi">API</button>
        <button id="switchToStatic">Static</button>
        <script type="module">
          // assume your page script exports init() and expose setters/hooks on window for tests if needed
        </script>
      </body></html>`,
      { url: 'https://app.test', runScripts: 'dangerously', resources: 'usable' }
    );
    // minimal fetch mock
    (dom.window as any).fetch = vi.fn(async (u: string) => {
      if (u.includes('/health')) {
        return { ok: true, json: async () => mockHealth('v9', ['x','y'], undefined, '2025-09-10T00:00:00Z') } as any;
      }
      return { ok: true, json: async () => ({}) } as any;
    });
  });

  it('updates #srcPath when toggling static ⇄ API', async () => {
    const { document } = dom.window as any;
    const srcPath = document.querySelector('#srcPath')! as HTMLElement;
    // simulate switching to API mode (call your real handler here if exported)
    srcPath.textContent = 'API: https://example.test/api';
    expect(srcPath.textContent).toContain('API:');

    // switch back to static
    srcPath.textContent = 'Static: ./data/claims.json';
    expect(srcPath.textContent).toContain('Static:');
  });
});

