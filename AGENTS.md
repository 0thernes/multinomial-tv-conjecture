# AGENTS.md — Canonical Agent Instructions (`multinomial-tv-conjecture`)

This file is the **single canonical instruction file** for all AI coding agents working in `multinomial-tv-conjecture` (`CLAUDE.md`, `GEMINI.md`, and `.cursor/rules/build-standard.mdc` point here).

## Project Identity & Mission

- **Repository:** `https://github.com/0thernes/multinomial-tv-conjecture`
- **Author:** Alexander Stephen Donahue (`Independent Researcher, Spokane, WA, USA`, ORCID `0009-0006-8168-9648`, email `0_0@0thernes.art`). **NEVER** reintroduce `0thernes LLC` (unformed legal entity).
- **Subject:** Complete Lean 4.35.0 formal proof (replayed in six checker runs via `lake comparator --paranoid`), independent exact/80-digit Python verification, interactive Blueprint, and AMS-LaTeX preprint proving **Conjecture 7.7** (`conj:atriangle`) and the quantitative $O(L^{-2})$ Lemma 7.3 remainder of Banić & Elezović (`arXiv:2610.17046v1`, 2026) together with the algebraic identities behind its cyclic corollary (`arXiv:2611.14735v1`, Theorem 3.10).
- **Licenses:** Code (`lean/`, `scripts/`, `tests/`, `.github/`) is **Apache-2.0** (`LICENSE`); manuscript and docs (`paper/`, `docs/`, `blueprint/`, `*.md`) are **CC-BY-4.0** (`LICENSE-DOCS`).

## Hard Rules (Build Standard v1.2.0 `R1`–`R8` & Verification Playbook v1.3)

1. **R1 / R2 (Solo-maintainer workflow):** Commit and push straight to `main`. Never create branch protection, PR templates, feature branches for routine work, commit signing requirements, or blocking git hooks.
2. **R3 (Informational CI):** All linters (`ruff`, `mypy`, `gitleaks`, Batteries `runLinter`) run report-only. Never fake a passing check.
3. **R4 (Zero banned files):** Never create `PULL_REQUEST_TEMPLATE.md`, `dependabot.yml`, `renovate.json`, `.github/copilot-instructions.md`, or `FUNDING.yml`.
4. **R5 / R6 (Zero fabrication):** Never fabricate `#print axioms` output, test passes, SHA-256 hashes, DOIs, arXiv IDs, or external peer-review claims. Always run the real tool on the current code.
5. **R7 (10-class finding taxonomy):** Classify every defect/finding into exactly one of: `bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot`.
6. **Lean soundness invariant:** Zero `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `@[extern]` in `lean/MultinomialTVConjecture/` or `lean/Solution.lean`. (`lean/Challenge.lean` intentionally holds 9 target `sorry` stubs verified against sorry-free `lean/Solution.lean` by `lake comparator`.)
7. **Single version source:** `VERSION` must match `CHANGELOG.md`, `CITATION.cff`, `formalization.yaml`, and `lean/lakefile.toml`.

## Repository Map

- `lean/MultinomialTVConjecture/` — Modular Lean 4.35.0 proof (`Combinatorial`, `StirlingRefined`, `GaussianEulerMaclaurin`, `LocalAsymptotics`, `Main`, `NonVacuity`).
- `lean/Challenge.lean`, `lean/Solution.lean`, `lean/comparator.json` — Isolated Mathlib-only target statements (9 targets) & comparator bridge (six checker runs).
- `lean/VerifyAxioms.lean` — Exhaustive `Lean.collectAxioms` metaprogram + explicit `#print axioms` audit.
- `paper/main.tex`, `paper/refs.bib` — AMS-LaTeX manuscript compiled via Tectonic to `dist/Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf`.
- `blueprint/src/content.tex` — Dependency blueprint validated against `lean/` by `scripts/build_blueprint.py`.
- `scripts/` — Exact/80-digit verifier (`verify_conjecture.py`), arXiv bundler (`build_arxiv_bundle.py`), audits (`check_readme_axioms.py`, `check_citations.py`, `Audit-Repo.ps1`, `audit-repo.sh`), Blueprint & Pages builders (`build_blueprint.py`, `build_site.py`), manifest generator (`generate_manifest.py`).
- `tests/` — Pytest ladder (exact rational, `hypothesis` property-based, negative, regression, golden, differential, metamorphic, numeric stability, mutation, repo integrity).
- `docs/` — Architecture, statement-fidelity table, verification, configuration, operations, threat model, ADRs, FAQ, glossary, run log, red-team review.

## Core Commands

```bash
just reproduce       # Clean end-to-end verification (numeric, pytest, citations, axioms, blueprint, site)
just verify-lean     # Lean build, forbidden scan, VerifyAxioms, README sync, comparator (six checker runs)
just test            # Full pytest suite
just paper           # Compile LaTeX manuscript & byte-reproducible arXiv tarball
just audit           # Score repo against Build Standard v1.2.0 (90 items)
```
