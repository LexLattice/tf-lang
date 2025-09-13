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
  health?: any;
  count?: any;
  list?: any;
  persistSource?: 'static' | 'api';
  offlineApi?: boolean;
} = {}) {
  const {
    staticData = BASE_DATA,
    health = {
      dataset_version: staticData.dataset_version,
      tags: staticData.tags || [],
      generated_at: staticData.generated_at,
      at: staticData.at
    },
    count = { n: staticData.claims.length },
    list = { items: staticData.claims },
    persistSource = 'static',
    offlineApi = false
  } = opts;
  const fetchCalls: string[] = [];
  const alerts: string[] = [];
  const htmlPath = fileURLToPath(new URL('../../../docs/claims-explorer.html', import.meta.url));
  const dom = await JSDOM.fromFile(htmlPath, {
    runScripts: 'dangerously',
    resources: 'usable',
    url: 'http://localhost/',
    beforeParse(window) {
      window.localStorage.setItem('tfl_source', persistSource);
      window.fetch = async (url: string | URL) => {
        const u = typeof url === 'string' ? url : url.toString();
        fetchCalls.push(u);
        const path = new URL(u, 'http://localhost').pathname;
        if (u.endsWith('claims-ro-mini.json')) {
          return new Response(JSON.stringify(staticData), { headers: { 'Content-Type': 'application/json' } });
        }
        if (offlineApi) throw new Error('offline');
        if (path.endsWith('/health')) {
          return new Response(JSON.stringify(health), { headers: { 'Content-Type': 'application/json' } });
        }
        if (path.endsWith('/claims/count')) {
          return new Response(JSON.stringify(count), { headers: { 'Content-Type': 'application/json' } });
        }
        if (path.endsWith('/claims/list')) {
          return new Response(JSON.stringify(list), { headers: { 'Content-Type': 'application/json' } });
        }
        throw new Error('network disabled');
      };
      window.alert = (msg: string) => { alerts.push(msg); };
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
  return { dom, window: dom.window, document: dom.window.document, fetchCalls, alerts };
}

describe('claims explorer', () => {
  it('renders identically across static and API sources and preserves state', async () => {
    const data = { ...BASE_DATA, tags: ['b', 'a'] };
    const { document, window, fetchCalls, dom } = await setup({
      staticData: data,
      health: { dataset_version: data.dataset_version, tags: data.tags, generated_at: data.generated_at, at: data.at }
    });
    const at = document.getElementById('at') as HTMLInputElement;
    expect(at.value).toBe('2025-09-09');
    const main = document.querySelector('main')!;
    const staticHTML = main.innerHTML;
    const panel = document.getElementById('tagsPanel')!;
    expect(panel.style.display).not.toBe('none');
    expect(fetchCalls.length).toBe(1);

    const sourceSel = document.getElementById('source') as HTMLSelectElement;
    sourceSel.value = 'api';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise<void>(resolve => {
      const check = () => {
        if (document.getElementById('srcPath')!.textContent === 'http://localhost:8787') resolve();
        else window.setTimeout(check, 0);
      };
      check();
    });
    await new Promise(r => window.setTimeout(r, 0));
    expect(at.value).toBe('2025-09-09');
    const apiHTML = main.innerHTML;
    expect(apiHTML).toBe(staticHTML);
    const before = fetchCalls.length;
    sourceSel.value = 'static';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise<void>(resolve => {
      const check = () => {
        if (document.getElementById('srcPath')!.textContent === './data/claims-ro-mini.json') resolve();
        else window.setTimeout(check, 0);
      };
      check();
    });
    await new Promise(r => window.setTimeout(r, 0));
    expect(fetchCalls.length).toBe(before);
    expect(main.innerHTML).toBe(staticHTML);
    dom.window.close();
  });

  it('falls back to generated_at for default dates', async () => {
    const staticData = { ...BASE_DATA, at: undefined };
    const { document, window, dom } = await setup({
      staticData,
      health: {
        dataset_version: staticData.dataset_version,
        tags: [],
        generated_at: '2024-01-02T00:00:00Z'
      }
    });
    const at = document.getElementById('at') as HTMLInputElement;
    expect(at.value).toBe('2025-09-09');
    at.value = '';
    const sourceSel = document.getElementById('source') as HTMLSelectElement;
    sourceSel.value = 'api';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise<void>(resolve => {
      const check = () => {
        if (document.getElementById('srcPath')!.textContent === 'http://localhost:8787') resolve();
        else window.setTimeout(check, 0);
      };
      check();
    });
    await new Promise(r => window.setTimeout(r, 0));
    expect(at.value).toBe('2024-01-02');
    dom.window.close();
  });

  it('hides tags panel when dataset has no tags', async () => {
    const { document, dom } = await setup({ staticData: BASE_DATA });
    const panel = document.getElementById('tagsPanel')!;
    expect(panel.style.display).toBe('none');
    dom.window.close();
  });

  it('handles API network failure gracefully', async () => {
    const { document, window, alerts, dom } = await setup({ offlineApi: true });
    const sourceSel = document.getElementById('source') as HTMLSelectElement;
    sourceSel.value = 'api';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise<void>(resolve => {
      const check = () => {
        if (document.getElementById('srcPath')!.textContent === 'http://localhost:8787') resolve();
        else window.setTimeout(check, 0);
      };
      check();
    });
    await new Promise(r => window.setTimeout(r, 0));
    expect(alerts.length).toBeGreaterThan(0);
    expect(document.getElementById('metricCount')!.textContent).toBe('0');
    dom.window.close();
  });
});
