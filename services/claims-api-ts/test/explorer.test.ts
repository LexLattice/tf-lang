import { describe, it, expect } from 'vitest';
import { JSDOM } from 'jsdom';
import { readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const root = join(__dirname, '../../..');
const baseDataset = JSON.parse(readFileSync(join(root, 'docs/data/claims-ro-mini.json'), 'utf8'));

async function makeDom(opts: {
  dataset?: any;
  apiCount?: any;
  apiList?: any;
  failApi?: boolean;
  dynamicApiList?: (call: number) => any;
} = {}) {
  const {
    dataset = baseDataset,
    apiCount = { n: 0 },
    apiList = { items: [] },
    failApi = false,
    dynamicApiList,
  } = opts;
  const html = readFileSync(join(root, 'docs/claims-explorer.html'), 'utf8');
  const fetchCalls: string[] = [];
  let listCall = 0;
  const fetchImpl = async (input: any): Promise<Response> => {
    const url = typeof input === 'string' ? input : input.url;
    fetchCalls.push(url);
    if (url.endsWith('claims-ro-mini.json')) {
      return new Response(JSON.stringify(dataset), { status: 200, headers: { 'Content-Type': 'application/json' } });
    }
    if (url.includes('/claims/count')) {
      if (failApi) throw new Error('offline');
      return new Response(JSON.stringify(apiCount), { status: 200, headers: { 'Content-Type': 'application/json' } });
    }
    if (url.includes('/claims/list')) {
      if (failApi) throw new Error('offline');
      const body = dynamicApiList ? dynamicApiList(listCall++) : apiList;
      return new Response(JSON.stringify(body), { status: 200, headers: { 'Content-Type': 'application/json' } });
    }
    throw new Error('unexpected ' + url);
  };
  const dom = new JSDOM(html, {
    runScripts: 'dangerously',
    resources: 'usable',
    url: 'http://localhost/',
    pretendToBeVisual: true,
    beforeParse(window) {
      (window as unknown as { fetch: typeof fetch }).fetch = fetchImpl;
    },
  });
  await new Promise(res => dom.window.addEventListener('load', () => res(null)));
  await new Promise(res => setTimeout(res, 0));
  return { dom, fetchCalls };
}

describe('claims explorer', () => {
  it('defaults dataset/date and hides tags when none', async () => {
    const { dom } = await makeDom();
    const doc = dom.window.document;
    expect((doc.querySelector('#at') as HTMLInputElement).value).toBe(baseDataset.at);
    expect(doc.getElementById('datasetVersion')!.textContent).toBe(baseDataset.dataset_version);
    expect(doc.getElementById('tagsPanel')!.style.display).toBe('none');
  });

  it('shows tags panel when dataset has tags', async () => {
    const withTags = {
      ...baseDataset,
      claims: baseDataset.claims.map((c: any, i: number) => (i === 0 ? { ...c, tags: ['foo'] } : c)),
    };
    const { dom } = await makeDom({ dataset: withTags });
    const panel = dom.window.document.getElementById('tagsPanel')!;
    expect(panel.style.display).not.toBe('none');
    expect(panel.textContent).toContain('foo');
  });

  it('source switch preserves state without reload', async () => {
    const { dom, fetchCalls } = await makeDom({
      apiCount: { n: baseDataset.claims.length },
      apiList: { items: baseDataset.claims },
    });
    const doc = dom.window.document;
    const at = doc.querySelector('#at') as HTMLInputElement;
    at.value = '2025-01-01';
    const srcSel = doc.querySelector('#source') as HTMLSelectElement;
    srcSel.value = 'api';
    srcSel.dispatchEvent(new dom.window.Event('change'));
    await new Promise(res => setTimeout(res, 0));
    expect(at.value).toBe('2025-01-01');
    const apiCalls = fetchCalls.filter(u => u.includes('/claims/')).length;
    srcSel.value = 'static';
    srcSel.dispatchEvent(new dom.window.Event('change'));
    await new Promise(res => setTimeout(res, 0));
    expect(at.value).toBe('2025-01-01');
    const apiCallsAfter = fetchCalls.filter(u => u.includes('/claims/')).length;
    expect(apiCallsAfter).toBe(apiCalls);
    expect(fetchCalls.filter(u => u.endsWith('claims-ro-mini.json')).length).toBe(1);
  });

  it('static mode works offline', async () => {
    const { dom } = await makeDom({ failApi: true });
    const count = dom.window.document.getElementById('metricCount')!.textContent;
    expect(count).toBe(String(baseDataset.claims.length));
  });

  it('renders deterministically across sources', async () => {
    const { dom } = await makeDom();
    const doc = dom.window.document;
    const first = doc.getElementById('rows')!.innerHTML;
    await dom.window.applyFilters();
    const second = doc.getElementById('rows')!.innerHTML;
    expect(second).toBe(first);

    const { dom: dom2 } = await makeDom({
      apiCount: { n: baseDataset.claims.length },
      dynamicApiList: call => ({ items: call % 2 === 0 ? baseDataset.claims : [...baseDataset.claims].reverse() }),
    });
    const doc2 = dom2.window.document;
    const srcSel = doc2.querySelector('#source') as HTMLSelectElement;
    srcSel.value = 'api';
    srcSel.dispatchEvent(new dom2.window.Event('change'));
    await new Promise(res => setTimeout(res, 0));
    const firstApi = doc2.getElementById('rows')!.innerHTML;
    await dom2.window.applyFilters();
    const secondApi = doc2.getElementById('rows')!.innerHTML;
    expect(secondApi).toBe(firstApi);
  });
});

