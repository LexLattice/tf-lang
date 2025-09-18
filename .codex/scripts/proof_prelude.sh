#!/usr/bin/env bash
set -Eeuo pipefail

# --- Resolve locations & output root (T3) ---
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

# Find repo root even if sourced from /workspace
if REPO_TOP="$(git rev-parse --show-toplevel 2>/dev/null)"; then
  REPO_ROOT="$REPO_TOP"
else
  # fallback: find a single child with .git (common in Codex: /workspace/tf-lang)
  REPO_ROOT="$PWD"
  for d in "$PWD"/*; do
    [ -d "$d/.git" ] && REPO_ROOT="$d" && break
  done
fi
cd "$REPO_ROOT"

OUT_ROOT="out/t3"
mkdir -p "$OUT_ROOT"

# Adopt any stray /workspace/out/t3 from pre-cd actions
if [ -d "$PWD/../out/t3" ] && [ ! -e "$OUT_ROOT/.adopted" ]; then
  rsync -a "$PWD/../out/t3/" "$OUT_ROOT/" 2>/dev/null || true
  touch "$OUT_ROOT/.adopted"
fi

# --- Feature flags ---
: "${ENABLE_WATCHERS:=1}"          # 1=on, 0=off
: "${ENABLE_CMD_TRACE:=0}"         # 1=on (interactive-only), 0=off
: "${ENABLE_CHECKPOINT_PUSH:=1}"   # 1=on, 0=off

# --- Budget & identity ---
: "${RUN_BUDGET_S:=1800}"
: "${RUN_START_ISO:=$(date -Iseconds)}"
: "${ACTOR:=agent}"
: "${RUN_ID:=$(date -u +%Y%m%dT%H%M%SZ)}"
START_EPOCH="$(date +%s)"
DEADLINE_EPOCH="$(( START_EPOCH + RUN_BUDGET_S ))"

# --- Logging helpers ---
json_event() {
  local kind="$1"; local msg="${2:-}"; local extra="${3:-}"
  local iso; iso="$(date -Iseconds)"; local ep; ep="$(date +%s)"
  printf '{"run_id":"%s","actor":"%s","event":"%s","ts":"%s","ts_epoch":%s,"msg":%s%s}\n' \
    "$RUN_ID" "$ACTOR" "$kind" "$iso" "$ep" "$(printf '%s' "$msg" | jq -Rs .)" "$extra" \
    | tee -a "$OUT_ROOT/_progress.log" >/dev/null
}
note() { json_event note "$*"; echo "- $(date -Iseconds) $*" >> AGENT_LOG.md; }

# --- Robust status writer (no set -e abort on jq) ---
status_update() {
  # Accept JSON string for stages; default {}
  local stages_json="${1:-{}}"
  local now_epoch; now_epoch="$(date +%s)"
  local used=$((now_epoch-START_EPOCH)); local rem=$((DEADLINE_EPOCH-now_epoch)); ((rem<0)) && rem=0
  local now_iso; now_iso="$(date -Iseconds)"

  set +e
  jq -n \
    --arg start "$RUN_START_ISO" \
    --arg nowi "$now_iso" \
    --argjson total "$RUN_BUDGET_S" \
    --argjson used "$used" \
    --argjson rem "$rem" \
    --arg stages "$stages_json" \
    '
    ($stages | fromjson? // {}) as $S
    | {
        plan: ["S1 idempotence","S2 conservation","S3 transport→parity"],
        stages: $S,
        budget: {start:$start, now:$nowi, total_s:$total, used_s:$used, remaining_s:$rem}
      }
    ' > "$OUT_ROOT/_status.json"
  local rc=$?
  set -e

  # Fallback if jq failed for any reason
  if [ $rc -ne 0 ]; then
    printf '{"plan":["S1 idempotence","S2 conservation","S3 transport→parity"],"stages":{},"budget":{"start":%s,"now":%s,"total_s":%s,"used_s":%s,"remaining_s":%s}}\n' \
      "$(printf '%s' "$RUN_START_ISO" | jq -Rs .)" \
      "$(printf '%s' "$now_iso"       | jq -Rs .)" \
      "$RUN_BUDGET_S" "$used" "$rem" \
      > "$OUT_ROOT/_status.json"
  fi
}

# --- Heartbeat (1/min) ---
heartbeat(){ while true; do sleep 60; json_event heartbeat ""; done; }
heartbeat & echo $! > "$OUT_ROOT/_heartbeat.pid"

# --- Start watchers if present (idempotent, gated) ---
start_bg(){ bash -lc "$1" & echo $! > "$2"; }
if [ "$ENABLE_WATCHERS" = "1" ]; then
  if ! { [ -f "$OUT_ROOT/_fs_watch.pid" ] && kill -0 "$(cat "$OUT_ROOT/_fs_watch.pid")" 2>/dev/null; }; then
    [ -x "$SCRIPT_DIR/fs_watch.sh" ] && start_bg "FS_EVENTS='create,modify,delete,move,close_write' \"$SCRIPT_DIR/fs_watch.sh\" '$REPO_ROOT'" "$OUT_ROOT/_fs_watch.pid"
  fi
  if ! { [ -f "$OUT_ROOT/_pause_watch.pid" ] && kill -0 "$(cat "$OUT_ROOT/_pause_watch.pid")" 2>/dev/null; }; then
    [ -x "$SCRIPT_DIR/pause_watch.sh" ] && start_bg "\"$SCRIPT_DIR/pause_watch.sh\" 90" "$OUT_ROOT/_pause_watch.pid"
  fi
fi

# --- Streamy runner wrappers (timeout + PTY + line buffering) ---
run() {
  local timeout_s=${TIMEOUT_S:-600}; local cmd="$*"
  json_event tool_start "$cmd"
  set +e
  if command -v script >/dev/null 2>&1; then
    script -q /dev/null -c "timeout $timeout_s bash -lc 'stdbuf -oL -eL $cmd'" 2>&1 | tee -a "$OUT_ROOT/_progress.log"
    rc=${PIPESTATUS[0]}
  else
    timeout "$timeout_s" bash -lc "stdbuf -oL -eL $cmd" 2>&1 | tee -a "$OUT_ROOT/_progress.log"
    rc=${PIPESTATUS[0]}
  fi
  set -e
  json_event tool_end "$cmd" ",\"rc\":$rc"
  return $rc
}
pn()   { run pnpm --reporter=append-only "$@"; }
ctest(){ run cargo test --workspace --all-targets -- --nocapture --quiet "$@"; }

# --- Command lifecycle tracer (safe, opt-in, interactive-only) ---
if [[ "$ENABLE_CMD_TRACE" = "1" && $- == *i* && -t 1 ]]; then
  __pc_old__="${PROMPT_COMMAND:-}"
  trace_pre() {
    [[ -n "${__TRACE_LOCK:-}" ]] && return
    __TRACE_LOCK=1
    __cmd_start__=$(date +%s%N)
    __cmd_str__=$BASH_COMMAND
    json_event cmd_start "$__cmd_str__" ",\"start_ns\":$__cmd_start__"
    unset __TRACE_LOCK
  }
  trap 'trace_pre' DEBUG
  PROMPT_COMMAND='__rc__=$?; if [[ -n "${__cmd_str__-}" ]]; then __end__=$(date +%s%N); __dur__=$((__end__-__cmd_start__)); json_event cmd_end "$__cmd_str__" ",\"rc\":$__rc__,\"dur_ns\":$__dur__"; unset __cmd_str__ __cmd_start__; fi; '"$__pc_old__"
fi

# --- First artifact guard (never-zero within ≤2m) ---
ensure_first_artifact() {
  (
    sleep 120
    if [ -z "$(find "$OUT_ROOT" -maxdepth 1 -type f ! -name '_*' 2>/dev/null)" ]; then
      local gitrev; gitrev="$(git rev-parse --short HEAD 2>/dev/null || echo null)"
      jq -n --arg ts "$(date -Iseconds)" --arg rev "$gitrev" \
        '{summary:{generated:$ts, git:$rev}, oracles:{}, seeds:{}}' > "$OUT_ROOT/oracles-report.json"
      echo "[guard] wrote skeleton $OUT_ROOT/oracles-report.json" >> "$OUT_ROOT/_progress.log"
    fi
  ) &
}
ensure_first_artifact

# --- Optional: early branch + draft PR + checkpoint pushes (single bootstrap) ---
if [ "$ENABLE_CHECKPOINT_PUSH" = "1" ] && git rev-parse --git-dir >/dev/null 2>&1; then
  : "${GIT_AUTHOR_NAME:=codex-agent}"
  : "${GIT_AUTHOR_EMAIL:=codex-agent@noreply}"
  : "${GIT_COMMITTER_NAME:=$GIT_AUTHOR_NAME}"
  : "${GIT_COMMITTER_EMAIL:=$GIT_AUTHOR_EMAIL}"

  # ensure out/ is ignored (avoid committing artifacts)
  grep -qxF 'out/' .gitignore 2>/dev/null || echo 'out/' >> .gitignore

  # Derive a sane base (avoid nesting proof/proof/…)
  BASE_BRANCH="$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo main)"
  if [[ "$BASE_BRANCH" == proof/*/* ]]; then
    BASE_BRANCH="$(printf '%s\n' "$BASE_BRANCH" | cut -d'/' -f2)"
  fi
  WORK_BRANCH="proof/${BASE_BRANCH}/${RUN_ID}"

  bootstrap_branch() {
    git switch -c "$WORK_BRANCH" 2>/dev/null || git switch "$WORK_BRANCH"
    git add -A
    git restore --staged out || true
    git commit -m "chore(proof): bootstrap run $RUN_ID" --allow-empty || true
    git push -u origin HEAD >/dev/null 2>&1 || true
    if command -v gh >/dev/null 2>&1 && gh auth status >/dev/null 2>&1; then
      gh pr create --draft --base "$BASE_BRANCH" --head "$WORK_BRANCH" \
        --title "Proof run $RUN_ID (auto)" \
        --body "Auto-started proof run from \`$BASE_BRANCH\`. Checkpoints will push here." >/dev/null 2>&1 || true
    fi
  }
  checkpoint() {
    local msg="$*"
    git add -A
    git restore --staged out || true
    git commit -m "chore(proof): $msg [run:$RUN_ID]" || true
    for i in 1 2 3; do git push >/dev/null 2>&1 && break || sleep $((i*2)); done
    if command -v gh >/dev/null 2>&1; then
      gh pr comment --edit-last --body "Checkpoint: $msg ($(date -Iseconds))" >/dev/null 2>&1 || true
    fi
  }
  export -f checkpoint

  # Only bootstrap once per run to avoid proof/proof chains
  if [ ! -f "$OUT_ROOT/.bootstrapped" ]; then
    bootstrap_branch
    touch "$OUT_ROOT/.bootstrapped"
  fi
fi

# --- Clean exit: stop background watchers ---
cleanup_watchers() {
  for f in "$OUT_ROOT/_heartbeat.pid" "$OUT_ROOT/_fs_watch.pid" "$OUT_ROOT/_pause_watch.pid"; do
    [ -f "$f" ] && kill "$(cat "$f")" 2>/dev/null || true
  done
}
trap cleanup_watchers EXIT

# --- Initial status & note ---
status_update '{}'   # safe now via fromjson? //
note "session_start (T3)"
