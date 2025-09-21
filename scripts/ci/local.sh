#!/usr/bin/env bash
set -Eeuo pipefail

# Local runner for GitHub Actions using nektos/act.
# Usage:
#   scripts/ci/local.sh list
#   scripts/ci/local.sh pr [--watch] [--privileged]
#   scripts/ci/local.sh push [--watch] [--privileged]
#   scripts/ci/local.sh workflow <path/to/workflow.yml> [--watch] [--privileged]
#   scripts/ci/local.sh job <job_name> [--watch] [--privileged]
#   scripts/ci/local.sh clean
#   scripts/ci/local.sh install-act
#
# Notes:
# - Reads .actrc for image pins, artifact path, offline mode, reuse.
# - Secrets from .github/.secrets (dotenv KEY=VALUE). Vars from .github/.vars.
# - On macOS ARM, forces linux/amd64 unless ACT_ARCH is set.

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT"

cmd_exists() { command -v "$1" >/dev/null 2>&1; }

ACT_CMD=""

locate_act() {
  if cmd_exists act; then
    ACT_CMD="$(command -v act)"
    return
  fi
  if [[ -x "$ROOT/bin/act" ]]; then
    ACT_CMD="$ROOT/bin/act"
    return
  fi
  ACT_CMD=""
}

die() { echo "ERROR: $*" >&2; exit 1; }

ensure_prereqs() {
  cmd_exists docker || die "Docker is required. Install Docker Desktop/Engine, then retry."
  locate_act
  if [[ -z "$ACT_CMD" ]]; then
    echo "act not found. Run: scripts/ci/local.sh install-act"
    exit 1
  fi
}

install_act() {
  locate_act
  if [[ -n "$ACT_CMD" ]]; then
    echo "act already installed at $ACT_CMD"
    exit 0
  fi
  OS="$(uname -s)"
  case "$OS" in
    Darwin)
      if cmd_exists brew; then
        brew install act
      else
        echo "On macOS, install Homebrew then: brew install act"
        exit 1
      fi
      ;;
    Linux)
      if cmd_exists act; then
        echo "act already installed."
      elif cmd_exists apt-get; then
        if [[ "${YES:-}" == "1" ]]; then
          curl -fsSL https://raw.githubusercontent.com/nektos/act/master/install.sh | sudo bash
        else
          echo "About to run the official 'act' installer with sudo."
          read -r -p "Continue? (y/N) " REPLY
          if [[ "$REPLY" =~ ^[Yy]$ ]]; then
            curl -fsSL https://raw.githubusercontent.com/nektos/act/master/install.sh | sudo bash
          else
            echo "Installation cancelled." >&2
            exit 1
          fi
        fi
      else
        echo "On Linux, install via your package manager or the installer above."
        exit 1
      fi
      ;;
    MINGW*|CYGWIN*|MSYS*)
      echo "On Windows: winget install nektos.act  (or use Scoop/Chocolatey)."
      exit 1
      ;;
    *)
      echo "Unsupported OS: $OS"
      exit 1
      ;;
  esac
  locate_act
  echo "act installed: ${ACT_CMD:-"(not found in PATH)"}"
}

arch_args() {
  if [[ "$(uname -s)" == "Darwin" && "$(uname -m)" == "arm64" && "${ACT_ARCH:-}" != "native" ]]; then
    echo "--container-architecture=linux/amd64"
  fi
}

secrets_args() {
  local args=()
  if [[ -f .github/.secrets ]]; then
    args+=(--secret-file .github/.secrets)
  else
    local tok=""
    if cmd_exists gh; then
      tok="$(gh auth token 2>/dev/null || true)"
    fi
    if [[ -n "${GITHUB_TOKEN:-}" ]]; then
      tok="${GITHUB_TOKEN}"
    fi
    if [[ -n "$tok" ]]; then
      args+=(-s "GITHUB_TOKEN=${tok}")
    else
      echo "NOTE: No .github/.secrets and no gh/GITHUB_TOKEN. Using placeholder; some steps may fail."
      args+=(-s "GITHUB_TOKEN=placeholder")
    fi
  fi

  if [[ -f .github/.vars ]]; then
    args+=(--var-file .github/.vars)
  fi
  printf "%s " "${args[@]}"
}

maybe_privileged() {
  for a in "$@"; do
    if [[ "$a" == "--privileged" ]]; then
      echo "--privileged"
      return
    fi
  done
}

ensure_dirs() {
  mkdir -p .artifacts .act
}

run_act() {
  local event="$1"; shift
  local extra_args=("$@")
  ensure_dirs
  "$ACT_CMD" "$event" $(arch_args) $(secrets_args) "${extra_args[@]}"
}

run_workflow() {
  local wf="$1"; shift
  [[ -f "$wf" ]] || die "Workflow not found: $wf"
  ensure_dirs
  "$ACT_CMD" -W "$wf" $(arch_args) $(secrets_args) "$@"
}

run_job() {
  local job="$1"; shift
  [[ -n "$job" ]] || die "Missing job name"
  ensure_dirs
  local ev_args=()
  if [[ -f .act/inputs.json ]]; then
    ev_args=(workflow_dispatch -e .act/inputs.json)
  else
    ev_args=(workflow_dispatch)
  fi
  "$ACT_CMD" -j "$job" "${ev_args[@]}" $(arch_args) $(secrets_args) "$@"
}

case "${1:-}" in
  install-act)
    install_act
    ;;
 list)
    ensure_prereqs
    ensure_dirs
    "$ACT_CMD" -l
    ;;
  pr)
    ensure_prereqs
    args=()
    [[ -f .act/pr.json ]] && args+=(-e .act/pr.json)
    [[ "${2:-}" == "--watch" ]] && args+=(-w -r) && shift
    priv="$(maybe_privileged "$@")"
    run_act pull_request "${args[@]}" ${priv:+$priv}
    ;;
  push)
    ensure_prereqs
    args=()
    [[ "${2:-}" == "--watch" ]] && args+=(-w -r) && shift
    priv="$(maybe_privileged "$@")"
    run_act push "${args[@]}" ${priv:+$priv}
    ;;
  workflow)
    ensure_prereqs
    wf="${2:-}"; shift 2 || true
    [[ -n "$wf" ]] || die "Usage: scripts/ci/local.sh workflow .github/workflows/ci.yml [--watch] [--privileged]"
    [[ "${1:-}" == "--watch" ]] && set -- -w -r "${@:2}"
    priv="$(maybe_privileged "$@")"
    run_workflow "$wf" ${priv:+$priv} "$@"
    ;;
  job)
    ensure_prereqs
    job="${2:-}"; shift 2 || true
    [[ -n "$job" ]] || die "Usage: scripts/ci/local.sh job <job_name> [--watch] [--privileged]"
    [[ "${1:-}" == "--watch" ]] && set -- -w -r "${@:2}"
    priv="$(maybe_privileged "$@")"
    run_job "$job" ${priv:+$priv} "$@"
    ;;
  clean)
    rm -rf .artifacts
    echo "Cleaned ./.artifacts"
    ;;
  *)
    cat <<'USAGE'
Usage:
  scripts/ci/local.sh list
  scripts/ci/local.sh pr [--watch] [--privileged]
  scripts/ci/local.sh push [--watch] [--privileged]
  scripts/ci/local.sh workflow <path/to/workflow.yml> [--watch] [--privileged]
  scripts/ci/local.sh job <job_name> [--watch] [--privileged]
  scripts/ci/local.sh clean
  scripts/ci/local.sh install-act

Tips:
- Use --privileged for jobs that build Docker images (Buildx/DinD).
- On Apple Silicon, linux/amd64 is forced unless ACT_ARCH=native.
USAGE
    ;;
esac
