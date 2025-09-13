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

async function setup(opts = {}) {
  const {
    staticData = BASE_DATA,
    health = { dataset_version: staticData.dataset_version, tags: [], at: staticData.at, generated_at: staticData.generated_at },
    count = { n: staticData.claims.length },
    list = { items: staticData.claims.map(c => ({ ...c, dataset_version: staticData.dataset_version })) },
    failApi = false
  } = opts;
  const fetchCalls = [];
  const alerts = [];
  const htmlPath = fileURLToPath(new URL('../../docs/claims-explorer.html', import.meta.url));
  const dom = await JSDOM.fromFile(htmlPath, {
    runScripts: 'dangerously',
    resources: 'usable',
    url: 'http://localhost/',
    beforeParse(window) {
      window.alert = msg => { alerts.push(String(msg)); };
      window.fetch = async url => {
        const u = typeof url === 'string' ? url : url.toString();
        fetchCalls.push(u);
        const path = new URL(u, 'http://localhost').pathname;
        if (u.endsWith('claims-ro-mini.json')) {
          return new Response(JSON.stringify(staticData), { headers: { 'Content-Type': 'application/json' } });
        }
        if (failApi) throw new Error('network disabled');
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
    }
  });
  await new Promise(resolve => {
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
  it('defaults to generated_at when at missing (offline static)', async () => {
    const data = { ...BASE_DATA };
    delete data.at;
    const { document, fetchCalls, dom } = await setup({ staticData: data });
    expect(document.getElementById('at').value).toBe('2025-09-09');
    expect(fetchCalls).toEqual([expect.stringMatching(/claims-ro-mini\.json$/)]);
    dom.window.close();
  });

  it('switches sources deterministically and preserves state', async () => {
    const { document, window, fetchCalls, dom } = await setup();
    const snapshot1 = document.getElementById('rows').innerHTML;
    const sourceSel = document.getElementById('source');
    sourceSel.value = 'api';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise(resolve => {
      const check = () => {
        if (fetchCalls.some(u => u.includes('/claims/list'))) resolve();
        else window.setTimeout(check, 0);
      };
      check();
    });
    const snapshot2 = document.getElementById('rows').innerHTML;
    expect(snapshot2).toBe(snapshot1);
    expect(document.getElementById('at').value).toBe('2025-09-09');
    expect(fetchCalls.some(u => u.includes('/health'))).toBe(true);
    expect(fetchCalls.some(u => u.includes('/claims/count'))).toBe(true);
    dom.window.close();
  });

  it('renders tags from health meta and ignores count tags', async () => {
    const { document, window, dom } = await setup({
      health: { dataset_version: 'api-1', tags: ['z', 'a'], generated_at: '2025-09-09T00:00:00Z' },
      count: { n: BASE_DATA.claims.length, tags: ['x'] }
    });
    const sourceSel = document.getElementById('source');
    sourceSel.value = 'api';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise(resolve => {
      const check = () => {
        const panel = document.getElementById('tagsPanel');
        if (panel.style.display !== 'none') resolve();
        else window.setTimeout(check, 0);
      };
      check();
    });
    const items = Array.from(document.querySelectorAll('#tagsList li')).map(li => li.textContent);
    expect(items).toEqual(['a', 'z']);
    dom.window.close();
  });

  it('handles API failure gracefully', async () => {
    const { document, window, alerts, dom } = await setup({ failApi: true });
    const sourceSel = document.getElementById('source');
    sourceSel.value = 'api';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise(r => window.setTimeout(r, 0));
    expect(document.getElementById('datasetVersion').textContent).toBe('unknown');
    expect(alerts.length).toBeGreaterThan(0);
    dom.window.close();
  });
});
