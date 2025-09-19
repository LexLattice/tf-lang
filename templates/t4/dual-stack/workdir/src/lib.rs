pub fn summarize_branch() -> String {
    format!(
        "Branch {branch} validates plan node {node}",
        branch = "{{branchName}}",
        node = "{{nodeId}}"
    )
}
