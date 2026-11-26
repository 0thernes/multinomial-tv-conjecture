# Errata and Version Corrections

This file records every factual, bibliographic, mathematical, or engineering error discovered after publication of any version, along with its exact fix and version tag.

## Errata Resolved in v2.0.0 (2026-11-25)

| ID | Class | Discovered In | Description | Resolution |
|---|---|---|---|---|
| `E-2026-001` | `error` | `v1.0.0` | `paper/refs.bib` entry `banic_elezovic_p1` listed truncated arXiv ID `2610.1336`, which arXiv zero-pads to `2610.01336` (*Hyperbolic Sphericity*, an unrelated paper). | Corrected to `arXiv:2610.13366` (*Discrete total variation under the multinomial, Part 1: expectation under the uniform null*) in `paper/refs.bib`, `CITATION.cff`, and `paper/main.tex`; added `scripts/check_citations.py` and regression test. |
| `E-2026-002` | `problem` | `v1.0.0` | Affiliation and copyright headers named `0thernes LLC`, an unformed legal entity as of November 2026. | Updated all active headers, `LICENSE`, `LICENSE-DOCS`, `CITATION.cff`, `formalization.yaml`, `README.md`, and `paper/main.tex` to `Alexander S. Donahue — Independent Researcher, Spokane, WA, USA` (ORCID `0009-0006-8168-9648`). |
| `E-2026-003` | `bug` | `v1.0.0` | `scripts/build_arxiv_bundle.py` docstring claimed `00README.XXX` was written into `dist/arxiv_submission.tar.gz`, but the code omitted it and left host `mtime`/UID/GID unnormalized. | Implemented explicit `00README.XXX` emission (`main.tex toplevel`) and deterministic `mtime=0, uid=0, gid=0` sorted tar writing, verified by automated tests. |
| `E-2026-004` | `hole` | `v1.0.0` | CI checked `#print axioms` with `grep -v` against a literal single-line string, missing wrapped lines, zero-axiom theorems, `native_decide`/`unsafe`, and README synchronization. | Replaced with `Lean.collectAxioms` metaprogram in `lean/VerifyAxioms.lean`, nested-comment/string-aware forbidden-token lexer, `scripts/check_readme_axioms.py`, and 6-kernel `lake comparator --paranoid`. |
| `E-2026-005` | `bug` | `v2.0.0` (draft) | Initial `v2.0.0` rewrite of `scripts/build_arxiv_bundle.py` omitted `paper/figures/*.pdf` referenced by `\includegraphics` in `paper/main.tex`. | Added deterministic `figures/*.pdf` packaging before `v2.0.0` release and verified clean standalone Tectonic compilation of extracted tarball. |

## Errata Resolved in v2.1.0 (2026-11-25)

| ID | Class | Discovered In | Description | Resolution |
|---|---|---|---|---|
| `E-2026-006` | `error` | `v2.0.0` | `docs/statement-fidelity.md` overstated exact rational Python check range as `L = 3..150` while `scripts/verify_conjecture.py` verifies `L = 3..45`; `REPLICATION.md` inaccurately listed `--inadvisably-no-sandbox` as 6-kernel Windows execution; `paper/main.tex` Table 1 omitted the 2-line `MultinomialTVConjecture.lean` row (causing column sum `5,443` vs total `5,445`). | Corrected `docs/statement-fidelity.md` to exact `L = 3..45`, corrected `REPLICATION.md` / `LIMITATIONS.md` / `docs/configuration.md` to reflect true Windows 5-kernel vs Linux 6-kernel execution, added `MultinomialTVConjecture.lean` (2 lines) to Table 1, and added automated regression guards in `tests/test_repo_integrity.py`. |
| `E-2026-007` | `bug` | `v2.0.0` | `scripts/Audit-Repo.ps1` `Test-TextFile` passed relative paths directly to `[System.IO.File]::OpenRead` (failing when invoked from another cwd); `scripts/check_citations.py` overwrote `results/citation-audit.json` with empty `online_checks: []` on offline CI runs; `blueprint/src/content.tex` listed 11 of 18 `NonVacuity` theorems and rendered raw backticks. | Fixed `Audit-Repo.ps1` with `[System.IO.Path]::Combine($Root, $f)`, guarded `check_citations.py` writes behind `--write` + Crossref retraction checks, listed all 18/18 `NonVacuity` theorems, rendered `<code>` cleanly, and upgraded Blueprint with interactive search/filter/dependency-cone highlighting. |
| `E-2026-008` | `issue` | `v2.0.0` | `results/lean-linter.log` and `docs/{configuration,threat-model}.md` leaked a local Windows workspace path, and `results/comparator-paranoid.log` retained the pre-CI Windows log instead of the verbatim 6-kernel Ubuntu CI output (`#45723630668`). | Replaced `results/comparator-paranoid.log` and `results/lean-linter.log` with clean verbatim Ubuntu CI outputs, removed all local path leaks, added live negative Lean kernel rejection in CI, expanded `data/MANIFEST.sha256` to 30 artifacts, and sealed it with a DigiCert RFC 3161 TSA timestamp (`data/MANIFEST.sha256.tsr`). |

## Errata Resolved in v2.2.0 (2026-11-25)

| ID | Class | Discovered In | Description | Resolution |
|---|---|---|---|---|
| `E-2026-009` | `bug` | `v2.1.0` | `scripts/verify_conjecture.py` `sums_abc_mp` hardcoded an `1e-85` early-exit threshold even at `120 dps`, silently truncating 120-digit sums at 85 digits, and omitted input-domain guards on `h_adj_direct_exact`, `sums_abc_exact`, `sums_abc_mp`, and `h_adj_1d_mp`. | Replaced hardcoded `1e-85` with dynamic `10^{-(mp.mp.dps + 10)}` and added strict `ValueError` domain validation with automated unit tests. |
| `E-2026-010` | `error` | `v2.1.0` | `docs/statement-fidelity.md` row `SF-2` mis-cited the exact 1D reduction as `Manuscript Sec. 3 (Theorems 3.1–3.3)` instead of `Manuscript Sec. 2 (Theorem 2.3, eqs. (2.11)–(2.13))`; `README.md` still cited `v2.0.0` Rekor `4114226539` and `v2.0.0` manuscript; `paper/main.tex` rendered `--paranoid` as en-dash `–paranoid` on pp. 1 & 17, omitted Claim `C6` in Table 2, and dropped clickable DOIs via `plain` BibTeX style. | Fixed `SF-2` anchor, synced all `v2.2.0` metadata and Rekor log references, switched to `{-}{-}paranoid`, `\usepackage{flafter}`, `\hypersetup` PDF metadata, `plainurl` clickable DOIs, and Claim `C6` in Table 2. |
| `E-2026-011` | `gap` / `hole` | `v2.1.0` | Lean files lacked Palomar-required Lean 4.35.0 `module` headers; source/TeX files lacked REUSE/SPDX headers; forbidden-token lexer missed `public axiom`/`partial def`; RFC 3161 test did not verify the 32-byte SHA-256 imprint; OpenTimestamps `.ots` proof was absent. | Migrated all 10 `.lean` files to `module` syntax (723 named + module-private theorems audited via `import all`), added REUSE/SPDX headers across all code/TeX files, hardened lexer & `check_readme_axioms.py` theorem-count parity, and added `scripts/stamp_timestamps.py` generating & cryptographically verifying both DigiCert `.tsr` and Bitcoin OpenTimestamps `.ots`. |

**Mathematical status:** Zero mathematical errors have been discovered in any theorem statement or proof of `v1.0.0`–`v2.2.0`; all 19 original Lean 4 theorems remain unchanged in mathematical content and pass all 6 independent kernels.

## Withdrawal Policy

If a mathematical flaw or statement-fidelity defect is ever discovered that invalidates a core claim in `CLAIMS.md`, the author commits to logging it here within 72 hours, tagging a corrected release, and posting an explicit retraction/erratum notice on GitHub Releases and any external preprint server where the manuscript has been deposited.
