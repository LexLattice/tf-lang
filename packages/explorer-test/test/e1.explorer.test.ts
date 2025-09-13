import { describe, it, expect } from 'vitest';
import { JSDOM } from 'jsdom';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const htmlPath = path.resolve(__dirname, '../../..', 'docs', 'claims-explorer.html');

async function loadDom(fetchImpl: (url: RequestInfo | URL) => Promise<Response>) {
  const html = fs.readFileSync(htmlPath, 'utf8');
  const dom = new JSDOM(html, {
    runScripts: 'dangerously',
    resources: 'usable',
    url: 'http://localhost/claims-explorer.html',
    pretendToBeVisual: true,
    beforeParse(window) {
      // @ts-ignore
      window.fetch = fetchImpl;
      window.navigator.clipboard = { writeText: async () => {} } as unknown as Clipboard;
    },
  });
  await new Promise<void>(resolve => {
    const check = () => {
      const txt = dom.window.document.getElementById('datasetVersion')!.textContent;
      if (txt && txt !== 'loading…') resolve();
      else dom.window.setTimeout(check, 0);
    };
    check();
  });
  return dom;
}

describe('E1 explorer', () => {
  it('loads defaults in static mode without network', async () => {
    const dataset = { dataset_version: 'v-static', at: '2024-01-01', claims: [ { id: 'A1', modality:'FORBIDDEN', jurisdiction:'RO', status:'determinate' } ] };
    const calls: string[] = [];
    const fetchStub = async (url: any) => {
      calls.push(String(url));
      if(String(url).includes('claims-ro-mini.json')){
        return { ok: true, json: async () => dataset } as Response;
      }
      throw new Error('network disabled');
    };
    const dom = await loadDom(fetchStub);
    const win = dom.window;
    expect(win.document.getElementById('datasetVersion')!.textContent).toBe('v-static');
    expect((win.document.getElementById('at') as HTMLInputElement).value).toBe('2024-01-01');
    expect(calls.length).toBe(1);
    dom.window.close();
  });

  it('switching source preserves state', async () => {
    const dataset = { dataset_version: 'v-static', at: '2024-01-01', claims: [ { id: 'A1', modality:'FORBIDDEN', jurisdiction:'RO', status:'determinate' } ] };
    const apiCount = { n: 1, dataset_version: 'v-api', tags: ['t'] };
    const apiList = { items: [ { id: 'A1', modality:'FORBIDDEN', jurisdiction:'RO', status:'determinate' } ] };
    const fetchStub = async (url: any) => {
      const u = String(url);
      if(u.includes('claims-ro-mini.json')) return { ok: true, json: async () => dataset } as Response;
      if(u.includes('/claims/count')) return { ok: true, json: async () => apiCount } as Response;
      if(u.includes('/claims/list')) return { ok: true, json: async () => apiList } as Response;
      throw new Error('unexpected '+u);
    };
    const dom = await loadDom(fetchStub);
    const win = dom.window;
    const atInput = win.document.getElementById('at') as HTMLInputElement;
    atInput.value = '2024-01-02';
    const beforeDoc = win.document;
    const sourceSel = win.document.getElementById('source') as HTMLSelectElement;
    sourceSel.value = 'api';
    sourceSel.dispatchEvent(new win.Event('change', { bubbles: true }));
    await new Promise<void>(resolve => {
      const check = () => {
        if(win.document.getElementById('datasetVersion')!.textContent === 'v-api') resolve();
        else win.setTimeout(check, 0);
      }; check();
    });
    expect(atInput.value).toBe('2024-01-02');
    expect(win.document).toBe(beforeDoc);
    dom.window.close();
  });

  it('tags panel visibility follows dataset tags', async () => {
    const tagged = { dataset_version: 'v-tag', at: '2024-01-01', tags:['X'], claims: [] };
    const bare = { dataset_version: 'v-bare', at: '2024-01-01', claims: [] };
    const fetchTagged = async (url:any) => ({ ok:true, json: async()=>tagged }) as Response;
    const fetchBare = async (url:any) => ({ ok:true, json: async()=>bare }) as Response;
    const dom1 = await loadDom(fetchBare);
    const win1 = dom1.window;
    expect(win1.document.getElementById('tagsPanel')!.style.display).toBe('none');
    dom1.window.close();
    const dom2 = await loadDom(fetchTagged);
    const win2 = dom2.window;
    expect(win2.document.getElementById('tagsPanel')!.style.display).not.toBe('none');
    expect(win2.document.getElementById('tagsList')!.textContent).toContain('X');
    dom2.window.close();
  });

  it('repeated renders are deterministic for both sources', async () => {
    const dataset = { dataset_version: 'v-static', at: '2024-01-01', claims: [ { id: 'A1', modality:'FORBIDDEN', jurisdiction:'RO', status:'determinate' } ] };
    const apiCount = { n: 1, dataset_version: 'v-api' };
    const apiList = { items: [ { id: 'A1', modality:'FORBIDDEN', jurisdiction:'RO', status:'determinate' } ], dataset_version: 'v-api' };
    const fetchStub = async (url:any) => {
      const u = String(url);
      if(u.includes('claims-ro-mini.json')) return { ok:true, json: async()=>dataset } as Response;
      if(u.includes('/claims/count')) return { ok:true, json: async()=>apiCount } as Response;
      if(u.includes('/claims/list')) return { ok:true, json: async()=>apiList } as Response;
      throw new Error('unexpected '+u);
    };
    const dom = await loadDom(fetchStub);
    const win = dom.window;
    const rows = win.document.getElementById('rows')!;
    const first = rows.innerHTML;
    await win.applyFilters();
    expect(rows.innerHTML).toBe(first);
    const sourceSel = win.document.getElementById('source') as HTMLSelectElement;
    sourceSel.value = 'api';
    sourceSel.dispatchEvent(new win.Event('change', { bubbles: true }));
    await new Promise<void>(resolve => {
      const check = () => {
        if(win.document.getElementById('datasetVersion')!.textContent === 'v-api') resolve();
        else win.setTimeout(check,0);
      }; check();
    });
    const firstApi = rows.innerHTML;
    await win.applyFilters();
    expect(rows.innerHTML).toBe(firstApi);
    dom.window.close();
  });
});
