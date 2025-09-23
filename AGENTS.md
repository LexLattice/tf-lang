For any task NODE_ID and phase CHECKPOINT:

1) Code only inside allowed paths (see meta/checker.yml and tf/blocks/<NODE_ID>/TF.yaml).
2) After each change, run:
   git diff -U0 --no-color | node tools/tf-lang-cli/index.mjs run "$NODE_ID" "$CHECKPOINT" --diff -
3) Read out/TFREPORT.json:
   - Any .results[rule].ok == false → fix just those items and re-run.
4) When GREEN, commit and move to the next checkpoint.
5) PR title format: node:<NODE_ID> cp:<CHECKPOINT>
