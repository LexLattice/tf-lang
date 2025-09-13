import { JSDOM } from 'jsdom';
import { describe, it, expect } from 'vitest';
import { fileURLToPath } from 'node:url';

const BASE_DATA = {
  dataset_version: 'ro-mini-0.1',
  generated_at: '2025-09-09T00:00:00Z',
  at: '2025-09-09',
  claims: [
    {
      id: 'C1',
      modality: 'FORBIDDEN',
      jurisdiction: 'RO',
      effective_from: '2024-01-01',
      effective_to: null,
      status: 'determinate',
      evidence: []
    }
  ],
  tags: ['t1', 't2']
};

async function setup(opts: {
  staticData?: any,
  health?: any,
  offline?: boolean
} = {}) {
  const { staticData = BASE_DATA, health, offline = false } = opts;
  const fetchCalls: string[] = [];
  const htmlPath = fileURLToPath(new URL('../../docs/claims-explorer.html', import.meta.url));
  const dom = await JSDOM.fromFile(htmlPath, {
    runScripts: 'dangerously',
    resources: 'usable',
    url: 'http://localhost/',
    beforeParse(window) {
      window.addEventListener('unhandledrejection', e => e.preventDefault());
      window.fetch = async (url: string | URL) => {
        const u = typeof url === 'string' ? url : url.toString();
        fetchCalls.push(u);
        const path = new URL(u, 'http://localhost').pathname;
        if (u.endsWith('claims-ro-mini.json')) {
          return new Response(JSON.stringify(staticData), { headers: { 'Content-Type': 'application/json' } });
        }
        if (offline) throw new Error('network disabled');
        if (path.endsWith('/health')) {
          return new Response(JSON.stringify(health ?? { dataset_version: staticData.dataset_version, tags: staticData.tags, generated_at: staticData.generated_at, at: staticData.at }), { headers: { 'Content-Type': 'application/json' } });
        }
        if (path.endsWith('/claims/count')) {
          return new Response(JSON.stringify({ n: staticData.claims.length }), { headers: { 'Content-Type': 'application/json' } });
        }
        if (path.endsWith('/claims/list')) {
          return new Response(JSON.stringify({ items: staticData.claims }), { headers: { 'Content-Type': 'application/json' } });
        }
        throw new Error('network disabled');
      };
    }
  });
  await new Promise<void>(resolve => {
    const check = () => {
      const dv = dom.window.document.getElementById('datasetVersion');
      if (dv && dv.textContent && dv.textContent !== 'loading…') resolve();
      else dom.window.setTimeout(check, 0);
    };
    check();
  });
  return { dom, window: dom.window, document: dom.window.document, fetchCalls };
}

describe('claims explorer', () => {
  it('renders identically across static and api sources with health meta', async () => {
    const { document, window, fetchCalls, dom } = await setup();
    const rowsStatic = document.getElementById('rows')!.innerHTML;
    const tagsStatic = document.getElementById('tagsPanel')!.outerHTML;
    const at = document.getElementById('at') as HTMLInputElement;
    const atVal = at.value;
    expect(document.getElementById('tagsPanel')!.style.display).not.toBe('none');

    const sourceSel = document.getElementById('source') as HTMLSelectElement;
    sourceSel.value = 'api';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise<void>(resolve => {
      const check = () => {
        if (document.getElementById('datasetVersion')!.textContent === 'ro-mini-0.1') resolve();
        else window.setTimeout(check, 0);
      };
      check();
    });
    const bodyApiRows = document.getElementById('rows')!.innerHTML;
    const bodyApiTags = document.getElementById('tagsPanel')!.outerHTML;
    expect(bodyApiRows).toBe(rowsStatic);
    expect(bodyApiTags).toBe(tagsStatic);
    expect(fetchCalls.some(u => u.includes('/health'))).toBe(true);
    expect(at.value).toBe(atVal);
    const calls = fetchCalls.length;
    sourceSel.value = 'static';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise<void>(resolve => {
      const check = () => {
        if (document.getElementById('datasetVersion')!.textContent === 'ro-mini-0.1') resolve();
        else window.setTimeout(check, 0);
      };
      check();
    });
    expect(document.getElementById('rows')!.innerHTML).toBe(rowsStatic);
    expect(fetchCalls.length).toBe(calls);
    await new Promise(r => window.setTimeout(r,0));
    dom.window.close();
  });

  it('defaults date from generated_at when at missing', async () => {
    const { document, dom } = await setup({ staticData: { ...BASE_DATA, at: undefined, tags: undefined } });
    const at = document.getElementById('at') as HTMLInputElement;
    expect(at.value).toBe('2025-09-09');
    expect(document.getElementById('tagsPanel')!.style.display).toBe('none');
    await new Promise(r => dom.window.setTimeout(r,0));
    dom.window.close();
  });

  it('handles offline static and graceful api failure', async () => {
    const { document, window, fetchCalls, dom } = await setup({ offline: true });
    expect(fetchCalls).toHaveLength(1);
    const sourceSel = document.getElementById('source') as HTMLSelectElement;
    sourceSel.value = 'api';
    await sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise(r => window.setTimeout(r, 0));
    expect(document.getElementById('datasetVersion')!.textContent).toBe('ro-mini-0.1');
    await new Promise(r => window.setTimeout(r,0));
    dom.window.close();
  });
});

