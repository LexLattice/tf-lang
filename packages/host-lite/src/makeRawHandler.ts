export type RawResult = { status: number; body: unknown };

export function makeRawHandler(deps: {
  makeHandler: (method: string, url: string, body: unknown) => Promise<RawResult> | RawResult;
}) {
  const handler = deps.makeHandler;
  return async (method: string, url: string, bodyStr: string): Promise<RawResult> => {
    try {
      const body = bodyStr == null || bodyStr === '' ? undefined : JSON.parse(bodyStr);
      return handler(method, url, body);
    } catch {
      return { status: 400, body: { error: 'bad_request' } };
    }
  };
}
