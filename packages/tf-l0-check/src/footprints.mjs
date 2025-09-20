// naive overlap: same uri string => conflict. Real impl should do pattern unification.
export function conflict(fpA=[], fpB=[]) {
  const writesA = new Set((fpA||[]).filter(x=>x.mode!=='read').map(x=>x.uri));
  const writesB = new Set((fpB||[]).filter(x=>x.mode!=='read').map(x=>x.uri));
  for (const u of writesA) if (writesB.has(u)) return true;
  return false;
}
