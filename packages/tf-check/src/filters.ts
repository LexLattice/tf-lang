export type Event = {
  runtime?: 'ts' | 'rust';
  ts?: number;
  region?: string;
  gate?: string;
  oracle?: string;
  tag?: any;
};

type Predicate = (event: Event) => boolean;

const TRUE: Predicate = () => true;

export function parseFilters(filters: string[]): Predicate {
  const tests: Predicate[] = [];
  for (const raw of filters) {
    const [key, value] = raw.split('=', 2);
    if (!key || value == null) continue;
    const values = value.split('|');
    if (key === 'region') {
      tests.push((event) => {
        const region = event.region ?? '';
        return values.some((val) => {
          if (val.endsWith('/**')) {
            return region.startsWith(val.slice(0, -3));
          }
          return region === val;
        });
      });
    } else if (key === 'tag') {
      tests.push((event) => {
        const tag = (event as any)?.tag ?? {};
        const kind = typeof tag === 'object' && tag ? tag.kind ?? tag.type ?? '' : '';
        return values.some((val) => {
          if (val.startsWith('!')) {
            return kind !== val.slice(1);
          }
          return kind === val;
        });
      });
    } else {
      tests.push((event) => {
        const field = (event as any)[key];
        return values.some((val) => {
          if (val.startsWith('!')) {
            return field !== val.slice(1);
          }
          return field === val;
        });
      });
    }
  }
  if (tests.length === 0) {
    return TRUE;
  }
  return (event) => tests.every((test) => test(event));
}

export function compilePredicate(source?: string): Predicate {
  if (!source) return TRUE;
  // Disable to avoid RCE; re-enable with a safe parser (e.g., jsep + whitelist).
  throw new Error('The --pred option is disabled for security reasons.');
}
