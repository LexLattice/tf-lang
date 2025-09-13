import { describe, it, expect, vi } from 'vitest';
import { JSDOM } from 'jsdom';
import fs from 'node:fs';
import path from 'node:path';

const html = fs.readFileSync(path.join(__dirname, '../../..', 'docs', 'claims-explorer.html'), 'utf8');
const tick = () => new Promise(res => setTimeout(res, 0));

describe('explorer source switching', () => {
  it('toggles sources with sane defaults and tags', async () => {
    const staticData = {
      dataset_version: 'sv1',
      at: '2025-01-02',
      tags: ['alpha'],
      claims: [
        { id: 'C1', modality: 'FORBIDDEN', jurisdiction: 'RO', status: 'determinate', effective_from: '2024-01-01', effective_to: null }
      ]
    };
    const apiCount = { n: 1 };
    const apiList = {
      items: [
        { id: 'A1', modality: 'PERMITTED', scope: { jurisdiction: 'RO' }, status: 'determinate', effective: { from: '2024-01-01', to: null }, evidence: [], explanation: null, dataset_version: 'api-v1' }
      ]
    };
    const apiHealth = { ok: true, dataset_version: 'api-v1', tags: [] };
    const fetchMock = vi.fn(async (url: string) => {
      const u = url.toString();
      if (u.endsWith('claims-ro-mini.json')) return { ok: true, json: async () => staticData };
      if (u.includes('/claims/count')) return { ok: true, json: async () => apiCount };
      if (u.includes('/claims/list')) return { ok: true, json: async () => apiList };
      if (u.includes('/health')) return { ok: true, json: async () => apiHealth };
      throw new Error('unexpected ' + u);
    });
    const dom = new JSDOM(html, {
      runScripts: 'dangerously',
      resources: 'usable',
      url: 'http://localhost/',
      beforeParse(win: any) { win.fetch = fetchMock; }
    });
    await tick();
    const doc = dom.window.document;
    expect(doc.querySelector('#datasetVersion')?.textContent).toBe('sv1');
    expect((doc.querySelector('#at') as HTMLInputElement).value).toBe('2025-01-02');
    expect(doc.getElementById('tagsPanel')).not.toBeNull();
    const staticRows = doc.querySelector('#rows')!.innerHTML;
    await dom.window.applyFilters();
    expect(doc.querySelector('#rows')!.innerHTML).toBe(staticRows);
    expect(fetchMock).toHaveBeenCalledTimes(1);

    const sourceSel = doc.querySelector('#source') as HTMLSelectElement;
    sourceSel.value = 'api';
    sourceSel.dispatchEvent(new dom.window.Event('change'));
    await tick();
    expect(doc.querySelector('#datasetVersion')?.textContent).toBe('api-v1');
    expect(doc.getElementById('tagsPanel')).toBeNull();
    expect((doc.querySelector('#at') as HTMLInputElement).value).toBe('2025-01-02');
    const callsAfterSwitch = fetchMock.mock.calls.length;
    expect(callsAfterSwitch).toBe(4);
    const apiRows = doc.querySelector('#rows')!.innerHTML;
    await dom.window.applyFilters();
    expect(doc.querySelector('#rows')!.innerHTML).toBe(apiRows);
    expect(fetchMock).toHaveBeenCalledTimes(7);

    sourceSel.value = 'static';
    sourceSel.dispatchEvent(new dom.window.Event('change'));
    await tick();
    expect(doc.querySelector('#datasetVersion')?.textContent).toBe('sv1');
    expect(doc.getElementById('tagsPanel')).not.toBeNull();
    expect((doc.querySelector('#at') as HTMLInputElement).value).toBe('2025-01-02');
    const staticRows2 = doc.querySelector('#rows')!.innerHTML;
    await dom.window.applyFilters();
    expect(doc.querySelector('#rows')!.innerHTML).toBe(staticRows2);
    expect(fetchMock).toHaveBeenCalledTimes(7);
  });

  it('renders offline in static mode', async () => {
    const staticData = {
      dataset_version: 'sv1',
      at: '2025-01-02',
      claims: [
        { id: 'C1', modality: 'FORBIDDEN', jurisdiction: 'RO', status: 'determinate', effective_from: '2024-01-01', effective_to: null }
      ]
    };
    const fetchMock = vi.fn(async (url: string) => {
      const u = url.toString();
      if (u.endsWith('claims-ro-mini.json')) return { ok: true, json: async () => staticData };
      throw new Error('network');
    });
    const dom = new JSDOM(html, {
      runScripts: 'dangerously',
      resources: 'usable',
      url: 'http://localhost/',
      beforeParse(win: any) { win.fetch = fetchMock; }
    });
    await tick();
    const doc = dom.window.document;
    expect(doc.querySelector('#datasetVersion')?.textContent).toBe('sv1');
    expect(doc.getElementById('tagsPanel')).toBeNull();
    expect(doc.querySelector('#metricCount')?.textContent).toBe('1');
    expect(fetchMock).toHaveBeenCalledTimes(1);
  });
});
