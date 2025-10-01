# TF-Lang v0.6 · Review entrypoint

## Track final reports
- [Track A · Platform scaffolding](A/docs.final.md)
- [Track B · Engine core](B/docs.final.md)
- [Track C · Checker & runtime](C/docs.final.md)
- [Track D · Examples & monitors](D/docs.final.md)
- [Track E · L1 macros & laws](E/docs.final.md)
- [Track F · Policy & auth](F/docs.final.md)
- [Track G · Release readiness](G/docs.final.md)
- [Track H · DX & docs](H/docs.final.md)

## Status matrix
| Track | Acceptance | Docs | Open blockers |
| --- | --- | --- | --- |
| A | RED | TBD | CLI alias friction and missing v0.6 quickstart keep the 10-minute flow broken. |
| B | RED | TBD | No `tf expand` front-door; inline comment parsing still crashes the expander. |
| C | RED | TBD | Runtime duplicates transform logic and lacks `tf run` entrypoint. |
| D | RED | TBD | `tasks/run-examples.sh` fails on inline comments; no example README. |
| E | RED | TBD | Law checkers ignore attached metadata; auth macros not exposed. |
| F | RED | TBD | Policy evaluate/enforce flows lack guidance and checker surface. |
| G | RED | TBD | Release gates undefined for typecheck/effects; manifests stale. |
| H | RED | TBD | Docs remain at v0.5; onboarding and glossary missing for v0.6. |

## Navigation
- [Synthesis logs](./_synthesis/INDEX.md)
- [Proposals](./_proposals/INDEX.md)
- [Top issues roll-up](./_summary/ALL.md)
