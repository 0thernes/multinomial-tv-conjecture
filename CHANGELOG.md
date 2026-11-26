# Changelog

All notable changes to this project are documented in this file.
Format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and Semantic Versioning (`VERSION` is the single source of truth).

## [2.1.0] - 2026-11-25

### Fixed
- **Audit-Repo.ps1 path bug (`bug`):** Fixed `Test-TextFile` to resolve relative paths via `[System.IO.Path]::Combine($Root, $f)` so cross-directory PowerShell audits pass cleanly.
- **Citation audit preservation & retraction checks (`bug`, `E-2026-007`):** Guarded `results/citation-audit.json` mutation behind `--write` so offline CI runs never erase live online verification records, and added live Crossref JSON retraction/withdrawal checking (`18/18` HTTP 200, `0` retractions).
- **Statement-fidelity, replication, and line-count parity (`error`, `E-2026-006`):** Aligned `docs/statement-fidelity.md` to exact `L = 3..45` (matching `verify_conjecture.py`), fixed `REPLICATION.md` / `LIMITATIONS.md` / `docs/configuration.md` to accurately distinguish native Windows 5-kernel checks from sandboxed Linux 6-kernel `lake comparator`, aligned `Challenge.lean` line count (`108` lines) everywhere, added `MultinomialTVConjecture.lean` (`2` lines) to `paper/main.tex` Table 1 so rows sum identically to `5,445`, split `b_1` and `b_2` Richardson error rows explicitly (`2.56e-55` / `2.53e-55`), and eliminated the residual `0.12pt` TeX overfull hbox (`0.00pt` max overfull).
- **Private local path leaks & verbatim CI logs (`issue`, `E-2026-008`):** Replaced `results/comparator-paranoid.log` and `results/lean-linter.log` with clean verbatim Ubuntu 24.04 6-kernel CI outputs (run `#45723630668`, Rekor `4114226539`) and removed local workstation path strings from `docs/configuration.md` and `docs/threat-model.md`.
- **Blueprint parity & rendering (`bug`):** Listed all `18/18` `NonVacuity` theorems in `blueprint/src/content.tex` (previously `11/18`) and fixed inline `\texttt{...}` / backtick code rendering in `scripts/build_blueprint.py`.
- **Windows subprocess UTF-8 safety (`blindspot`):** Enforced `encoding="utf-8"` on subprocess calls in `tests/test_repo_integrity.py` and `PYTHONUTF8: "1"` in `.github/workflows/ci.yml`.

### Added
- **Live negative Lean kernel rejection check in CI (`.github/workflows/lean-verify.yml`):** Compiles a deliberately false statement (`aTriangle = 1/32`) on every CI run and asserts the Lean 4.35.0 kernel rejects it, plus SLSA/Sigstore attestation of BOTH `lean-axioms-ci.log` and `comparator-paranoid-ci.log`.
- **Interactive Lean Blueprint controls (`scripts/build_blueprint.py`):** Live search bar, Stage 1–5 filter buttons, stage color legend, and click-to-highlight transitive dependency cone (upstream ancestors + downstream descendants + connecting Bezier edges) with verified MathJax SRI.
- **Expanded cryptographic manifest & DigiCert RFC 3161 TSA timestamp:** Expanded `data/MANIFEST.sha256` from 13 to 30 core proof, paper, blueprint, verifier, and log artifacts, sealed with a verifiable DigiCert RFC 3161 timestamp (`data/MANIFEST.sha256.tsr`) and included in GitHub Releases.
- **Playbook v1.3 completeness:** Added `docs/literature-search.md` (Pass 4), `scripts/generate_llms_full.py`, full 10-Pass Review Scorecard in `docs/reviews/red-team-2026-11-25.md`, `main.bbl` guard in `scripts/build_arxiv_bundle.py`, and 7 new automated regression tests in `tests/test_repo_integrity.py`.

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
