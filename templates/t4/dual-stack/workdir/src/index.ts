export interface BranchContext {
  readonly branchName: string;
  readonly nodeId: string;
}

export function describeBranch(context: BranchContext): string {
  return `Branch ${context.branchName} evaluates plan node ${context.nodeId}.`;
}

export const CURRENT_BRANCH = "{{branchName}}";
export const PLAN_NODE_ID = "{{nodeId}}";
