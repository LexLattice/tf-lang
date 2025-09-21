import { effectOf, effectRank, commuteSymmetric } from '../../tf-l0-check/src/effect-lattice.mjs';

export function normalizeByCommutation(ir, catalog) {
  return visit(ir, catalog);
}

function visit(node, catalog) {
  if (!node || typeof node !== 'object') {
    return node;
  }

  if (node.node === 'Seq') {
    const originalChildren = Array.isArray(node.children) ? node.children : [];
    const normalizedChildren = originalChildren.map(child => visit(child, catalog));
    const childChanged = normalizedChildren.some((child, idx) => child !== originalChildren[idx]);
    const commuted = commuteSeqChildren(normalizedChildren, catalog);
    const reordered = commuted !== normalizedChildren;
    if (!childChanged && !reordered) {
      return node;
    }
    return { ...node, children: commuted };
  }

  if (Array.isArray(node.children)) {
    const originalChildren = node.children;
    const normalizedChildren = originalChildren.map(child => visit(child, catalog));
    const changed = normalizedChildren.some((child, idx) => child !== originalChildren[idx]);
    if (!changed) {
      return node;
    }
    return { ...node, children: normalizedChildren };
  }

  return node;
}

function commuteSeqChildren(children, catalog) {
  if (!Array.isArray(children) || children.length < 2) {
    return children;
  }

  const nodes = children.slice();
  let changed = false;
  let swapped = true;

  while (swapped) {
    swapped = false;
    for (let i = 0; i < nodes.length - 1; i++) {
      const left = nodes[i];
      const right = nodes[i + 1];
      if (!isPrim(left) || !isPrim(right)) {
        continue;
      }

      const leftEffect = effectOf(left.prim, catalog);
      const rightEffect = effectOf(right.prim, catalog);
      if (!commuteSymmetric(leftEffect, rightEffect)) {
        continue;
      }

      if (shouldSwap(left, leftEffect, right, rightEffect)) {
        nodes[i] = right;
        nodes[i + 1] = left;
        swapped = true;
        changed = true;
      }
    }
  }

  return changed ? nodes : children;
}

function shouldSwap(leftNode, leftEffect, rightNode, rightEffect) {
  const leftRank = effectRank(leftEffect);
  const rightRank = effectRank(rightEffect);
  if (rightRank < leftRank) {
    return true;
  }
  if (rightRank > leftRank) {
    return false;
  }

  const leftPrim = typeof leftNode?.prim === 'string' ? leftNode.prim : '';
  const rightPrim = typeof rightNode?.prim === 'string' ? rightNode.prim : '';
  return rightPrim < leftPrim;
}

function isPrim(node) {
  return node && typeof node === 'object' && node.node === 'Prim';
}
