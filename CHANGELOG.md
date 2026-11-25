# Changelog

All notable changes to this project are documented in this file.
Format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and Semantic Versioning (`VERSION` is the single source of truth).

## [2.0.0] - 2026-11-25

### Fixed
- **Citation error (`error`):** Corrected `banic_elezovic_p1` in `paper/refs.bib` from truncated `arXiv:2610.1336` (which resolved to an unrelated paper `2610.01336`) to `arXiv:2610.13366`; added `scripts/check_citations.py` to prevent citation regressions.
- **Affiliation accuracy (`problem`):** Replaced unformed-entity references (`0thernes LLC`) with `Independent Researcher, Spokane, WA, USA` matching ORCID `0009-0006-8168-9648`.
- **arXiv bundler bug (`bug`):** Updated `scripts/build_arxiv_bundle.py` to actually emit `00README.XXX` as documented and normalize tarball metadata (`mtime=0`, `uid=0`, `gid=0`, sorted members) for byte-reproducible archives.
- **Axiom check fragility (`hole`):** Replaced brittle `grep -v` axiom check in CI with exhaustive `Lean.collectAxioms` metaprogram (`VerifyAxioms.lean`), comment/string-aware forbidden-token scanning, and `scripts/check_readme_axioms.py` verbatim sync check.

### Added
- **Palomar-compatible 6-kernel verification package:** Isolated Mathlib-only `lean/Challenge.lean`, sorry-free `lean/Solution.lean`, `lean/comparator.json`, `formalization.yaml`, and live `lake comparator --config comparator.json --paranoid` runs across all 6 kernels (`Lean 4.35.0`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
- **Non-vacuity & adversarial definition tests (`lean/MultinomialTVConjecture/NonVacuity.lean`):** 18 machine-checked witnesses proving exact rational values `hAdj 0..5`, strict sign/separation bounds, 3 false-constant refutations, and `n = 5` witnesses for linear and cyclic `γ`.
- **Lean 4 Dependency Blueprint & GitHub Pages portal:** `blueprint/src/content.tex`, `scripts/build_blueprint.py`, `scripts/build_site.py`, and `.github/workflows/pages.yml`.
- **Full Build Standard v1.2.0 & Verification Playbook v1.3 compliance:** `repo.yaml`, `repo-standard.schema.json`, `VERSION`, `CLAIMS.md`, `LIMITATIONS.md`, `REPLICATION.md`, `ERRATA.md`, `ROADMAP.md`, `AGENTS.md`, `CLAUDE.md`, `GEMINI.md`, `.cursor/rules/build-standard.mdc`, `llms.txt`, `llms-full.txt`, `justfile`, `docs/` suite (including `statement-fidelity.md`, ADRs, threat model, red-team review), `scripts/{Audit-Repo.ps1,audit-repo.sh,audit-checks.tsv,dev.sh,generate_manifest.py}`, cross-platform CI (`ubuntu`/`windows`/`macos`), `SHA256SUMS` + Sigstore SLSA release workflow.
- **Python verification & test ladder (`tests/`):** Exact rational, `hypothesis` property-based, negative, regression, golden snapshot, differential/oracle, metamorphic, numerical stability, mutation self-check, `ruff`, and `mypy`.
- **Manuscript v2.0.0 upgrades (`paper/main.tex`):** Numbered Claims Ledger, Statement-Fidelity Audit Table, 6-Kernel Verification & Non-Vacuity section, CRediT roles & AI disclosure, COI, Limitations & Threats to Validity, and Versioning/Errata/Withdrawal note.

### Changed
- **Dual license (`issue`):** Re-licensed code/Lean/scripts from MIT to **Apache-2.0** (`LICENSE`, aligning with Mathlib4) while keeping manuscripts/docs under **CC-BY-4.0** (`LICENSE-DOCS`), with explicit `NOTICE` and `THIRD_PARTY_NOTICES.md`.

## [1.0.0] - 2026-11-18

### Added
- Initial complete Lean 4.35.0 proof of Conjecture 7.7 of Banić & Elezović (`arXiv:2610.17046v1`), 19-page AMS-LaTeX preprint, 80-digit Python verification script (`scripts/verify_conjecture.py`), and arXiv bundle generator.
