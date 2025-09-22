// @tf-test kind=infra area=pages speed=fast deps=node
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

const DATA_WITH_TAGS = { ...BASE_DATA, tags: ['t2', 't1'] };

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
  it('renders identically across sources and preserves state', async () => {
    const { document, window, fetchCalls, dom } = await setup({ staticData: DATA_WITH_TAGS });
    const at = document.getElementById('at') as HTMLInputElement;
    expect(at.value).toBe('2025-09-09');
    expect(fetchCalls).toHaveLength(1);
    const bodyStatic = document.body.innerHTML;
    const tagsStatic = Array.from(document.getElementById('tagsList')!.children).map(li => (li as HTMLElement).textContent);
    expect(tagsStatic).toEqual(['t1', 't2']);

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
    expect(at.value).toBe('2025-09-09');
    const bodyApi = document.body.innerHTML;
    const tagsApi = Array.from(document.getElementById('tagsList')!.children).map(li => (li as HTMLElement).textContent);
    expect(tagsApi).toEqual(['t1', 't2']);
    expect(bodyApi).toBe(bodyStatic);

    const before = fetchCalls.length;
    sourceSel.value = 'static';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise(r => window.setTimeout(r, 0));
    expect(document.body.innerHTML).toBe(bodyStatic);
    expect(fetchCalls.length).toBe(before);
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

  it('renders tags panel only when tags exist', async () => {
    const { document, dom } = await setup();
    expect(document.getElementById('tagsPanel')!.style.display).toBe('none');
    dom.window.close();

    const data = { ...BASE_DATA, tags: ['t2', 't1'] };
    const { document: doc2, dom: dom2 } = await setup({ staticData: data });
    const panel = doc2.getElementById('tagsPanel')!;
    expect(panel.style.display).not.toBe('none');
    const tags = Array.from(doc2.getElementById('tagsList')!.children).map(li => (li as HTMLElement).textContent);
    expect(tags).toEqual(['t1', 't2']);
    dom2.window.close();
  });

  it('renders deterministically across reloads and sources', async () => {
    const { document: d1, dom: dom1 } = await setup({ staticData: DATA_WITH_TAGS });
    const body1 = d1.body.innerHTML;

    const { document: d2, window: w2, dom: dom2 } = await setup({ staticData: DATA_WITH_TAGS });
    const src = d2.getElementById('source') as HTMLSelectElement;
    src.value = 'api';
    src.dispatchEvent(new w2.Event('change'));
    await new Promise<void>(resolve => {
      const check = () => {
        if (d2.getElementById('datasetVersion')!.textContent === 'ro-mini-0.1') resolve();
        else w2.setTimeout(check, 0);
      };
      check();
    });
    const body2 = d2.body.innerHTML;
    await new Promise(r => w2.setTimeout(r, 0));
    dom1.window.close();
    dom2.window.close();
    expect(body2).toBe(body1);
  });
});
