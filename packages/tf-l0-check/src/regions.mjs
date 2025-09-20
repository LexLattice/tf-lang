// Region enforcement stubs
// - Authorize: any primitive whose id/name matches protected list must be nested in an Authorize region.
export function checkRegions(ir, catalog, protectedList=[]) {
  const reasons = [];
  function visit(node, regionStack) {
    if (!node) return;
    if (node.node === 'Region') {
      const next = regionStack.concat([node.kind]);
      for (const c of node.children||[]) visit(c, next);
      return;
    }
    if (node.node === 'Prim') {
      const name = (node.prim||'').toLowerCase();
      const protectedHit = protectedList.some(p => name.includes(p));
      const inAuth = regionStack.includes('Authorize');
      if (protectedHit && !inAuth) {
        reasons.push(`Protected op '${name}' must be inside Authorize{}`);
      }
      return;
    }
    for (const c of node.children||[]) visit(c, regionStack);
  }
  visit(ir, []);
  return { ok: reasons.length === 0, reasons };
}
