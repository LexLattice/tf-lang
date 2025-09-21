# Local GitHub Actions with `act`

## Install
- Docker Desktop/Engine
- `act` (run `scripts/ci/local.sh install-act`)

## Quickstart
```bash
# list jobs from all workflows
bash scripts/ci/local.sh list

# run full PR pipeline (uses .act/pr.json if present)
bash scripts/ci/local.sh pr

# run specific workflow file
bash scripts/ci/local.sh workflow .github/workflows/ci.yml

# run a single job (uses workflow_dispatch + .act/inputs.json)
bash scripts/ci/local.sh job build

# rebuild on changes and reuse containers
bash scripts/ci/local.sh pr --watch
```

## Secrets & Vars

* Copy `.github/.secrets.example` → `.github/.secrets`, fill in values.
* Copy `.github/.vars.example` → `.github/.vars` for non-secrets.
* If no secrets file is present, we try `gh auth token` or fallback placeholder.

## Docker/image builds

If your job uses Buildx/DinD, pass `--privileged`:

```bash
bash scripts/ci/local.sh job docker_build --privileged
```

## Skipping external side-effects locally

In workflows, you *may* guard deploy/notify steps:

```yaml
if: ${{ !env.ACT }}
```

`act` sets `ACT=1` during local runs.
