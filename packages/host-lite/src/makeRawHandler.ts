export type RawResult = { status: number; body: unknown };

export function makeRawHandler(deps: {
  makeHandler: (method: string, url: string, body: unknown) => Promise<RawResult> | RawResult;
}) {
  const handler = deps.makeHandler;
  return async (method: string, url: string, bodyStr: string): Promise<RawResult> => {
    if (method !== 'POST' || (url !== '/plan' && url !== '/apply')) {
      return { status: 404, body: { error: 'not_found' } };
    }
    let body: unknown;
    try {
      body = JSON.parse(bodyStr || '{}');
    } catch {
      return { status: 400, body: { error: 'bad_request' } };
    }
    return handler(method, url, body);
  };
}

