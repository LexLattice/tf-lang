import { effectOf, effectRank, commuteSymmetric } from '../../tf-l0-check/src/effect-lattice.mjs';
import { canonicalize } from './hash.mjs';

export function normalizeByCommutation(ir, catalog) {
  return visit(ir, catalog ?? {});
}

function visit(node, catalog) {
  if (!node || typeof node !== 'object') {
    return node;
  }

  if (node.node === 'Seq') {
    const originalChildren = Array.isArray(node.children) ? node.children : [];
    let changed = false;
    const normalizedChildren = originalChildren.map((child) => {
      const next = visit(child, catalog);
      if (next !== child) {
        changed = true;
      }
      return next;
    });
    const { nodes: reordered, changed: reorderedChanged } = reorderSequentialChildren(normalizedChildren, catalog);
    if (reorderedChanged) {
      changed = true;
    }
    if (!changed && !reorderedChanged) {
      return node;
    }
    const resultChildren = reorderedChanged ? reordered : normalizedChildren;
    return { ...node, children: resultChildren };
  }

  if (node.node === 'Par' || node.node === 'Region') {
    const originalChildren = Array.isArray(node.children) ? node.children : [];
    let changed = false;
    const normalizedChildren = originalChildren.map((child) => {
      const next = visit(child, catalog);
      if (next !== child) {
        changed = true;
      }
      return next;
    });
    if (!changed) {
      return node;
    }
    return { ...node, children: normalizedChildren };
  }

  if (Array.isArray(node.children)) {
    const originalChildren = node.children;
    let changed = false;
    const normalizedChildren = originalChildren.map((child) => {
      const next = visit(child, catalog);
      if (next !== child) {
        changed = true;
      }
      return next;
    });
    if (!changed) {
      return node;
    }
    return { ...node, children: normalizedChildren };
  }

  return node;
}

function reorderSequentialChildren(children, catalog) {
  const nodes = children.slice();
  let anySwapped = false;
  if (nodes.length < 2) {
    return { nodes, changed: false };
  }

  let passSwapped = false;
  do {
    passSwapped = false;
    for (let i = 0; i < nodes.length - 1; i++) {
      const a = nodes[i];
      const b = nodes[i + 1];
      if (!isPrim(a) || !isPrim(b)) {
        continue;
      }
      const famA = effectOf(a.prim, catalog);
      const famB = effectOf(b.prim, catalog);
      if (!commuteSymmetric(famA, famB)) {
        continue;
      }
      if (shouldSwapSequentialPair(a, b, famA, famB)) {
        nodes[i] = b;
        nodes[i + 1] = a;
        passSwapped = true;
        anySwapped = true;
      }
    }
  } while (passSwapped);

  return { nodes, changed: anySwapped };
}

function isPrim(node) {
  return node && typeof node === 'object' && node.node === 'Prim' && typeof node.prim === 'string';
}

function shouldSwapSequentialPair(nodeA, nodeB, famA, famB) {
  const rankA = effectRank(famA);
  const rankB = effectRank(famB);
  if (rankB < rankA) {
    return true;
  }
  if (rankB > rankA) {
    return false;
  }

  const primA = typeof nodeA.prim === 'string' ? nodeA.prim : '';
  const primB = typeof nodeB.prim === 'string' ? nodeB.prim : '';
  if (primB < primA) {
    return true;
  }
  if (primB > primA) {
    return false;
  }

  const argsKeyA = canonicalize(nodeA.args ?? null);
  const argsKeyB = canonicalize(nodeB.args ?? null);
  return argsKeyB < argsKeyA;
}
