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
  ]
};

async function setup(opts: {
  staticData?: any;
  apiMeta?: any;
  failApi?: boolean;
} = {}) {
  const { staticData = BASE_DATA, apiMeta, failApi = false } = opts;
  const fetchCalls: string[] = [];
  const htmlPath = fileURLToPath(new URL('../../docs/claims-explorer.html', import.meta.url));
  const dom = await JSDOM.fromFile(htmlPath, {
    runScripts: 'dangerously',
    resources: 'usable',
    url: 'http://localhost/',
    beforeParse(window) {
      window.fetch = async (url: string | URL) => {
        const u = typeof url === 'string' ? url : url.toString();
        fetchCalls.push(u);
        const path = new URL(u, 'http://localhost').pathname;
        if (u.endsWith('claims-ro-mini.json')) {
          return new Response(JSON.stringify(staticData), { headers: { 'Content-Type': 'application/json' } });
        }
        if (path.endsWith('/health')) {
          if (failApi) throw new Error('offline');
          const meta = apiMeta || {
            dataset_version: staticData.dataset_version,
            tags: staticData.tags || [],
            at: staticData.at,
            generated_at: staticData.generated_at
          };
          return new Response(JSON.stringify(meta), { headers: { 'Content-Type': 'application/json' } });
        }
        if (path.endsWith('/claims/count')) {
          if (failApi) throw new Error('offline');
          return new Response(
            JSON.stringify({ n: staticData.claims.length }),
            { headers: { 'Content-Type': 'application/json' } }
          );
        }
        if (path.endsWith('/claims/list')) {
          if (failApi) throw new Error('offline');
          return new Response(
            JSON.stringify({ items: staticData.claims }),
            { headers: { 'Content-Type': 'application/json' } }
          );
        }
        throw new Error('network disabled');
      };
    }
  });
  await new Promise<void>(resolve => {
    const check = () => {
      const dv = dom.window.document.getElementById('datasetVersion');
      if (dv && dv.textContent !== 'loading…') resolve();
      else dom.window.setTimeout(check, 0);
    };
    check();
  });
  return { dom, window: dom.window, document: dom.window.document, fetchCalls };
}

describe('claims explorer', () => {
  it('renders tags deterministically across sources', async () => {
    const data = { ...BASE_DATA, tags: ['t2', 't1'] };
    const apiMeta = { dataset_version: data.dataset_version, tags: ['t1', 't2'], at: data.at, generated_at: data.generated_at };
    const { document, window, dom } = await setup({ staticData: data, apiMeta });
    const tagsStatic = Array.from(document.getElementById('tagsList')!.children).map(li => (li as HTMLElement).textContent);
    expect(tagsStatic).toEqual(['t1', 't2']);
    const bodyStatic = document.body.innerHTML;

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
    const tagsApi = Array.from(document.getElementById('tagsList')!.children).map(li => (li as HTMLElement).textContent);
    expect(tagsApi).toEqual(['t1', 't2']);
    const bodyApi = document.body.innerHTML;
    expect(bodyApi).toBe(bodyStatic);
    dom.window.close();
  });

  it('static mode works offline and API errors gracefully', async () => {
    const { document, window, fetchCalls, dom } = await setup({ failApi: true });
    expect(document.getElementById('datasetVersion')!.textContent).toBe('ro-mini-0.1');
    expect(fetchCalls).toHaveLength(1);
    const sourceSel = document.getElementById('source') as HTMLSelectElement;
    sourceSel.value = 'api';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise(r => window.setTimeout(r, 0));
    expect(document.getElementById('datasetVersion')!.textContent).toBe('ro-mini-0.1');
    dom.window.close();
  });

  it('uses generated_at when at missing', async () => {
    const data = { ...BASE_DATA };
    delete data.at;
    const { document, dom } = await setup({ staticData: data });
    const at = document.getElementById('at') as HTMLInputElement;
    expect(at.value).toBe('2025-09-09');
    dom.window.close();
  });

  it('hides tags panel when dataset has no tags', async () => {
    const { document, window, dom } = await setup();
    expect(document.getElementById('tagsPanel')!.style.display).toBe('none');
    const sourceSel = document.getElementById('source') as HTMLSelectElement;
    sourceSel.value = 'api';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise(r => window.setTimeout(r, 0));
    expect(document.getElementById('tagsPanel')!.style.display).toBe('none');
    dom.window.close();
  });
});
