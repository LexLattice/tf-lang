# optional TF wrapper (0.45 can use CLI directly)
# Seq {
#   tf:ci/check_scope@1 { diff_path = env.DIFF_PATH, config = "meta/checker.yml" }
#   tf:rules/expand@1 { rulebook = "tf/blocks/A1-LSP-Proto/rulebook.yml", checkpoint = input.checkpoint }
#   tf:ci/run_selected_probes@1 { selected = "out/rules.selected.json", artifacts = input.artifacts }
#   tf:report/emit@1 { out = "out/TFREPORT.json" }
# }
