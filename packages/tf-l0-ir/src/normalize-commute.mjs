import { effectOf, effectRank, commuteSymmetric } from '../../tf-l0-check/src/effect-lattice.mjs';

export function normalizeByCommutation(ir, catalog = {}) {
  const catalogSafe = catalog || {};
  return walk(ir);

  function walk(node) {
    if (!node || typeof node !== 'object') {
      return node;
    }

    if (node.node === 'Seq') {
      const children = (node.children ?? []).map(walk);
      const ordered = bubble(children);
      return { ...node, children: ordered };
    }

    if (node.node === 'Region' || node.node === 'Par') {
      return { ...node, children: (node.children ?? []).map(walk) };
    }

    if (Array.isArray(node.children)) {
      return { ...node, children: node.children.map(walk) };
    }

    return node;
  }

  function bubble(children) {
    if (children.length <= 1) {
      return children;
    }

    const nodes = children.slice();
    let swapped = true;

    while (swapped) {
      swapped = false;
      for (let i = 0; i < nodes.length - 1; i++) {
        const left = nodes[i];
        const right = nodes[i + 1];
        if (!isPrim(left) || !isPrim(right)) {
          continue;
        }

        const famLeft = effectOf(left.id || left.prim, catalogSafe);
        const famRight = effectOf(right.id || right.prim, catalogSafe);
        if (!commuteSymmetric(famLeft, famRight)) {
          continue;
        }

        const rankLeft = effectRank(famLeft);
        const rankRight = effectRank(famRight);
        const primLeft = typeof left.prim === 'string' ? left.prim : '';
        const primRight = typeof right.prim === 'string' ? right.prim : '';

        if (rankRight < rankLeft || (rankRight === rankLeft && primRight < primLeft)) {
          nodes[i] = right;
          nodes[i + 1] = left;
          swapped = true;
        }
      }
    }

    return nodes;
  }
}

function isPrim(node) {
  return node && node.node === 'Prim';
}
