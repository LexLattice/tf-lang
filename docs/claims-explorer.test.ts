import { JSDOM } from 'jsdom';
import { describe, it, expect } from 'vitest';
import { fileURLToPath } from 'node:url';

const BASE_DATA = {
  dataset_version: 'ro-mini-0.1',
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

async function setup(staticData = BASE_DATA, apiVersion = 'api-1', apiTags: string[] = []) {
  const fetchCalls: string[] = [];
  const htmlPath = fileURLToPath(new URL('./claims-explorer.html', import.meta.url));
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
        if (path.endsWith('/claims/count')) {
          return new Response(
            JSON.stringify({ dataset_version: apiVersion, n: staticData.claims.length, tags: apiTags }),
            { headers: { 'Content-Type': 'application/json' } }
          );
        }
        if (path.endsWith('/claims/list')) {
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
  it('switches sources and stays deterministic', async () => {
    const { document, window, fetchCalls, dom } = await setup();
    const at = document.getElementById('at') as HTMLInputElement;
    expect(at.value).toBe('2025-09-09');
    expect(document.getElementById('datasetVersion')!.textContent).toBe('ro-mini-0.1');
    expect(document.getElementById('tagsPanel')!.style.display).toBe('none');
    expect(fetchCalls.length).toBe(1);

    const sourceSel = document.getElementById('source') as HTMLSelectElement;
    sourceSel.value = 'api';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise<void>(resolve => {
      const check = () => {
        if (document.getElementById('datasetVersion')!.textContent === 'api-1') resolve();
        else window.setTimeout(check, 0);
      };
      check();
    });
    expect(at.value).toBe('2025-09-09');
    expect(fetchCalls.some(u => new URL(u, 'http://localhost').pathname.endsWith('/claims/count'))).toBe(true);
    expect(fetchCalls.some(u => new URL(u, 'http://localhost').pathname.endsWith('/claims/list'))).toBe(true);
    const rows = document.getElementById('rows')!;
    const apiFirst = rows.innerHTML;
    document.getElementById('mod')!.dispatchEvent(new window.Event('change'));
    await new Promise(r => window.setTimeout(r, 0));
    expect(rows.innerHTML).toBe(apiFirst);

    const before = fetchCalls.length;
    sourceSel.value = 'static';
    sourceSel.dispatchEvent(new window.Event('change'));
    await new Promise<void>(resolve => {
      const check = () => {
        if (document.getElementById('datasetVersion')!.textContent === 'ro-mini-0.1') resolve();
        else window.setTimeout(check, 0);
      };
      check();
    });
    expect(fetchCalls.length).toBe(before);
    const staticFirst = rows.innerHTML;
    document.getElementById('mod')!.dispatchEvent(new window.Event('change'));
    await new Promise(r => window.setTimeout(r, 0));
    expect(rows.innerHTML).toBe(staticFirst);
    dom.window.close();
  });

  it('shows tags panel when dataset has tags', async () => {
    const data = { ...BASE_DATA, tags: ['t1', 't2'] };
    const { document, dom } = await setup(data);
    const panel = document.getElementById('tagsPanel')!;
    expect(panel.style.display).not.toBe('none');
    expect(document.getElementById('tagsList')!.children.length).toBe(2);
    dom.window.close();
  });
});

