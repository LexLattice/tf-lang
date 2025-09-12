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

setup:
	pnpm i --frozen-lockfile=false
	git config core.hooksPath .githooks

build:
	pnpm -C packages/claims-core-ts build
	pnpm -C packages/adapter-legal-ts build
	pnpm -C packages/tf-lang-l0-ts build

test:
	pnpm -C packages/tf-lang-l0-ts test
	cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml
	bash tests/test_prbundle.sh

golden:
	scripts/golden.sh

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
	bash ./scripts/prbundle.sh -r "$(REPO)" $$OUTARG $(PRS)
