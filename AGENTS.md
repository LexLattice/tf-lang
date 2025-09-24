For any task `NODE_ID` and phase `CHECKPOINT`:

1. **Edit only inside allowed paths**
   See `meta/checker.yml` and `tf/blocks/<NODE_ID>/TF.yaml`. The checker will hard-fail if you touch files outside scope.&#x20;

2. **After each change, run the checkpoint with a stable, staged diff** *(the one habit)*

   * Stage your changes (or the minimal subset you want to validate):

     ```bash
     git add -A
     ```
   * Pipe the **staged** diff (exclude build artifacts) into the checker:

     ```bash
     git diff --cached -U0 --no-color -- . ':(exclude)dist/**' \
       | node tools/tf-lang-cli/index.mjs run "$NODE_ID" "$CHECKPOINT" --diff -
     ```

   > Why staged? It makes the diff deterministic, avoids empty-diff edge cases, and keeps token/scope checks crisp.

   Fixtures policy: samples/a1/** and scripts/lsp-smoke/** are read-only after cp1. If you need a different sample, propose it in a meta PR. The checker enforces this in cp2+.

3. **Act only on failing rules, then re-run step 2**

   * Open `out/TFREPORT.json`; fix **only** the rules where `.results[rule].ok == false`.
   * If you hit the token rule with **no code changes** showing up, re-stage (empty diffs are blocked by design).

4. **When GREEN, commit and move to the next checkpoint**
   Suggested message:

   ```
   chore(<NODE_ID>/<CHECKPOINT>): green
   ```



5. **If opening a PR, use this title**

   ```
   node:<NODE_ID> cp:<CHECKPOINT>
   ```

   CI will replay the same checkpoint deterministically.&#x20;

---

## Helper (optional)

Add this shell helper to iterate quickly:

```bash
run_checkpoint() {
  local CP="$1"
  git add -A >/dev/null 2>&1 || true
  git diff --cached -U0 --no-color -- . ':(exclude)dist/**' \
    | node tools/tf-lang-cli/index.mjs run "$NODE_ID" "$CP" --diff - \
    || { echo "RED — failing rules:"; jq -r '.results|to_entries[]|select(.value.ok==false)|.key' out/TFREPORT.json; cat out/TFREPORT.json; return 3; }
}
```

---

**Notes**

* You don’t need to remember policies; the checkpoint contract encodes them. Just **run the checkpoint** and fix what it reports.
* If you truly need to adjust the rulebook or TF.yaml for the node, do it in the **meta** phase (when available) or as a separate meta change—otherwise scope guard will block.
