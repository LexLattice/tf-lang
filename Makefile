SHELL := /usr/bin/env bash

.PHONY: help setup build test golden api docs-up docker-up docker-down

help:
	@echo "Targets:"
	@echo "  setup       - install deps and enable git hooks"
	@echo "  build       - build TS packages"
	@echo "  test        - run TS tests and Rust tests"
	@echo "  golden      - run golden behavior check"
	@echo "  api         - start claims API (PORT=8787)"
	@echo "  docs-up     - serve docs via Python http.server on :8080"
	@echo "  docker-up   - docker compose up --build"
	@echo "  docker-down - docker compose down"
	@echo "  collect-reports - aggregate parallel run reports"
	@echo "  pass-report     - write pass summary to docs/runs"
	@echo "  pack-pass       - copy pass artifacts under docs/runs/pack-pass"
	@echo "  winner          - show path to RUNS_REPORTS.md"
	@echo "  knowledge       - index .codex/knowledge into docs/runs/knowledge.md"
	@echo "  release-notes   - draft release notes into docs/runs/release-notes.md"
	@echo "  sync-agents     - sync role blocks into AGENTS.md"
	@echo "  git-clean-refs  - purge stale PR refs and sanitize repo config"
	@echo "  git-sanitize-config - remove PR refspecs from .git/config"

setup:
	pnpm install --frozen-lockfile
	git config core.hooksPath .githooks

build:
	pnpm -C packages/claims-core-ts build
	pnpm -C packages/adapter-legal-ts build
	pnpm -C packages/tf-lang-l0-ts build

test:
	pnpm -C packages/tf-lang-l0-ts test
	cargo test --locked --manifest-path packages/tf-lang-l0-rs/Cargo.toml
	bash tests/test_prbundle.sh

golden:
	@bash ./.codex/scripts/golden.sh

api:
	pnpm -C services/claims-api-ts build || true
	PORT?=8787 HOST?=0.0.0.0 pnpm -C services/claims-api-ts start

docs-up:
	cd docs && python -m http.server 8080

docker-up:
	docker compose up --build

docker-down:
	docker compose down

REPO ?= LexLattice/tf-lang
OUT  ?=
PRS  ?=

.PHONY: prbundle
prbundle:
	@if [ -z "$(PRS)" ]; then \
	  echo "Usage: make prbundle PRS='19-22'  (or '19 20 21 22', or mixed '19-20 22')"; \
	  echo "Default output: docs/pr/pr<PRS>.md (e.g., pr19_22.md)"; \
	  echo "Override: REPO=owner/repo OUT=file.md"; \
	  exit 2; \
	fi
	@if [ -n "$(OUT)" ]; then OUTARG="-o $(OUT)"; else OUTARG=""; fi; \
	bash ./.codex/scripts/prbundle.sh -r "$(REPO)" $$OUTARG $(PRS)

collect-reports:
	@./.codex/scripts/collect-run-reports.sh --prs $(PRS)
# usage:
#  with explicit labels:
#    make collect-reports PRS="30:A 31:B 32:C 33:D"
#  or let the script auto-label A/B/C/D by PR number:
#    make collect-reports PRS="30 31 32 33"
#  (labels are optional; ordering is numeric by PR)

briefs-check:
	@python3 .codex/scripts/lint-briefs.py

briefs-index:
	@python3 .codex/scripts/build-index.py

sync-agents:
	@bash ./.codex/scripts/sync-agents.sh
# First-time setup:
#   chmod +x .codex/scripts/sync-agents.sh
#   yq --version   # ensure installed

# Use bash for nicer conditionals
SHELL := /usr/bin/env bash
HOT_UPDATE := .codex/scripts/hot-update.sh

.PHONY: hot-update
hot-update:
	@# Guard required vars
	@if [ -z "$(RUN)" ] || [ -z "$(PR)" ]; then \
		echo "Usage: make hot-update RUN=D1_2 PR=70-73 [REPO=owner/repo] [REMOTE=origin] [COMMIT=1] [MSG='...']"; \
		exit 2; \
	fi
	@if [ ! -x "$(HOT_UPDATE)" ]; then \
		echo "Error: $(HOT_UPDATE) not found or not executable."; \
		echo "Make sure it exists and run: chmod +x $(HOT_UPDATE)"; \
		exit 3; \
	fi
	@set -euo pipefail; \
	declare -a FLAGS=(); \
	[ -n "$(REPO)" ]   && FLAGS+=(-r "$(REPO)"); \
	[ -n "$(REMOTE)" ] && FLAGS+=(--remote "$(REMOTE)"); \
	[ -n "$(COMMIT)" ] && FLAGS+=(--commit); \
	[ -n "$(MSG)" ]    && FLAGS+=(-m "$(MSG)"); \
	echo "→ Running hot update: RUN=$(RUN) PR=$(PR) $${FLAGS[*]}"; \
	"$(HOT_UPDATE)" "$(RUN)" "$(PR)" "$${FLAGS[@]}"

.PHONY: hot-update-commit
hot-update-commit:
	@$(MAKE) hot-update COMMIT=1 MSG="$(or $(MSG),codex: hot review ($(RUN) $(PR)))" RUN="$(RUN)" PR="$(PR)" REPO="$(REPO)" REMOTE="$(REMOTE)"


# Optional: open the reviews folder after generating (requires VS Code)
.PHONY: hot-open
hot-open:
	@code .codex/reviews || true

pass-bodies:
	@./.codex/scripts/pass-bodies.sh $(GROUP) $(PRS)
# usage:
#   make pass-bodies GROUP="F1_1" PRS="78-81"
#   make pass-bodies GROUP="E2_1" PRS="74:A 75:B 76:C 77:D"

# Additional codex helper targets
.PHONY: pass-report pack-pass winner knowledge release-notes
pass-report:
	@bash ./.codex/scripts/pass-report.sh

pack-pass:
	@bash ./.codex/scripts/pack-pass.sh

winner:
	@bash ./.codex/scripts/winner.sh

knowledge:
	@bash ./.codex/scripts/knowledge.sh

release-notes:
	@bash ./.codex/scripts/release-notes.sh

.PHONY: git-clean-refs git-sanitize-config
git-clean-refs:
	@bash ./.codex/scripts/git-clean-refs.sh

git-sanitize-config:
	@bash ./.codex/scripts/git-clean-refs.sh --sanitize-config
