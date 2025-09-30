function normalizeSet(values = []) {
  return Array.from(new Set(values)).sort();
}

function mergeSets(a = [], b = []) {
  return normalizeSet([...a, ...b]);
}

export function checkSampleCrdtMerge() {
  const samples = [
    { a: ['a'], b: ['b'], c: ['c'] },
    { a: ['x', 'y'], b: ['y', 'z'], c: ['q'] },
    { a: [], b: ['alpha'], c: ['beta', 'gamma'] },
  ];
  const results = samples.map((sample) => {
    const left = mergeSets(sample.a, mergeSets(sample.b, sample.c));
    const right = mergeSets(mergeSets(sample.a, sample.b), sample.c);
    const idempotent = normalizeSet(sample.a);
    const assocOk = JSON.stringify(left) === JSON.stringify(right);
    const idempOk = JSON.stringify(mergeSets(sample.a, sample.a)) === JSON.stringify(idempotent);
    return {
      sample,
      assocOk,
      idempOk,
      ok: assocOk && idempOk,
    };
  });
  return {
    ok: results.every((r) => r.ok),
    results,
  };
}

export default checkSampleCrdtMerge;
