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

## Errata Resolved in v2.3.0 (2026-11-26)

| ID | Class | Discovered In | Description | Resolution |
|---|---|---|---|---|
| `E-2026-012` | `error` | `v2.2.0` | `scripts/build_site.py` hardcoded `576` audited theorems on the live GitHub Pages portal instead of parsing `results/lean-axioms-all.log`; `llms.txt`, `docs/media/social-preview.svg`, and `.github/ISSUE_TEMPLATE/bug.yml` still displayed `v2.0.0`; `README.md` cited `v2.1.0` Rekor `4116347212`; `results/comparator-paranoid.log` retained `v2.0.0` run `#45723630668`. | Replaced hardcoded counts in `scripts/build_site.py` with dynamic parsing of `results/lean-axioms-all.log` and `NonVacuity.lean`, refreshed `results/comparator-paranoid.log` to verbatim `v2.2.0` run `#45747471704` (Rekor `4117130014`), synced all version/Rekor strings, and added permanent automated regression tests. |
| `E-2026-013` | `error` | `v2.2.0` | `docs/literature-search.md` still listed pre-deduplication `18/18` citation checks (`6` arXiv IDs + `12` DOIs) and `61 STAT-*` Mega-Atlas entries instead of exact deduplicated `16/16` (`4` unique arXiv IDs + `12` DOIs) and `59 STAT-*` problems in Mega-Atlas V2 (`v2.7.0`). | Corrected `docs/literature-search.md` against `results/citation-audit.json` and `MegaAtlas_Unsolved_Problems_V2.tsv` (`1,900` total, `59` `STAT-*`). |
| `E-2026-014` | `conflict` / `gap` | `v2.2.0` | GitHub `automated-security-fixes` remained enabled (violating Build Standard `R4`); `lean/lakefile.toml` omitted `weak.linter.mathlibStandardSet = true` (Playbook #5) and SPDX lines inside `/- ... -/` triggered Mathlib's `linter.style.header`; Corollary 1.2(iii) (`gamma(3;N)`, `gamma(4;N)`) remained prose-only outside Lean. | Disabled `automated-security-fixes`, enabled `weak.linter.mathlibStandardSet = true` with clean `-- SPDX-*` separation (0 warnings across all 10 files), formally proved `gamma3_closed_form` & `gamma4_closed_form` across all 6 kernels (`8` comparator targets, `20` NonVacuity witnesses, `730` audited theorems), and added strict CSP + pinned SHA-256 `osv-scanner v2.7.1`. |

**Mathematical status:** Zero mathematical errors have been discovered in any Lean theorem statement or proof of `v1.0.0`–`v2.3.0`; all original Lean 4 theorems remain unchanged in mathematical content and pass all six comparator checker runs alongside the newly formalized Corollary 1.2(iii) identities. The 2026-11-26 statement audit (below) found errors of citation, scope and wording, not in the mathematics.

## 2026-11-26 statement audit

An independent statement audit of commit `0a69443` was run on 2026-11-26. Audit log: <https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md>. It found that the Lean statement of Conjecture 7.7 matches the source clause by clause and that no earlier proof was found. It also found the errors below. None of them changes a Lean theorem statement.

### Corrected in this pass (documentation)

| Where | What was wrong | Correction |
|---|---|---|
| `README.md`, `CLAIMS.md`, `LIMITATIONS.md`, `docs/faq.md`, `docs/statement-fidelity.md` | Part 5 (`arXiv:2611.14735v1`) cited as "Theorem 5.2"; no such theorem exists in v1. | The conditional `γ_c(n)` result is Theorem 3.10. |
| `docs/literature-search.md` (2026-11-18 row) | Part 5 "Remarks 5.3, 5.5, 6.3" cited as confirming the conjecture open; in v1 these are unrelated or absent. | Remarks 3.11, 3.13 and 4.3. |
| `README.md`, `docs/faq.md`, `docs/index.md`, `docs/architecture.md` | Source described without its status. | It is an arXiv v1 preprint (posted 2026-10-12, no journal reference), not peer reviewed. |
| `README.md`, `docs/faq.md` | The γ formulas were called "unconditional" consequences, and Lean was said to verify them. | Lean checks four algebraic identities. The variance statements still rest on Part 2 Theorem 7.6, Lemmas 7.2, 7.3, 7.5 and Section 8, and Part 5 Theorem 3.10, which are cited and not formalized. |
| `README.md`, `CLAIMS.md`, `docs/verification.md` | "730 named and module-private theorems". | 157 author-written theorems and lemmas; the axiom audit covers all 730 theorem constants, 573 of them compiler-generated. |
| `README.md`, `CLAIMS.md`, `LIMITATIONS.md`, `docs/` | "Six independent kernels". | Six checker runs of `lake comparator --paranoid`; two of them are the Lean kernel (paranoid and default mode). |
| `README.md`, `docs/verification.md` | A "live negative Lean kernel rejection check" was cited as evidence. | That CI step supplies a proof of a different statement and passes on any error; it tests nothing about falsity. The refutation of `aTriangle = 1/32` is the proved theorem `adversarial_aTriangle_ne_one_div_32`. |
| `README.md` | "Verbatim output" of `VerifyAxioms.lean`. | Excerpt: 21 of the 49 `depends on axioms` lines and the summary line. |
| `README.md`, `LIMITATIONS.md` | "0 warnings". | No warnings except the 8 intentional `sorry` warnings of the statement-only `Challenge.lean`. |
| `README.md` | Targets 5–8 said to state Corollary 1.2(i)–(iii) "verbatim". | Target 7 uses an equal rearrangement of the source's left side; in target 8 the term `(−1)^N/(2π)` is carried on both sides, not derived. |
| `README.md`, `docs/statement-fidelity.md`, `LIMITATIONS.md` | "20 non-vacuity witnesses" presented as definition checks. | 6 test the definition `hAdj` directly; 14 are corollaries of the proved closed forms. |
| `CLAIMS.md` C6, `docs/literature-search.md` | "All 16 bibliographic references" verified. | 16 identifiers (4 arXiv IDs, 12 DOIs) covering 15 of 16 entries; one book has no identifier; theorem numbers are not checked by the script. |
| `docs/statement-fidelity.md` SF-5 | Theorem 7.6 located at "p. 35". | Printed p. 59 (Conjecture 7.7 is on p. 60). |
| `README.md` | Release status cited Rekor `4127149586` for `v2.3.0` without saying which commit. | Tag `v2.3.0` points to `a1d84d7`; the committed comparator log is from CI run `45830919144` at that commit. The audited commit `0a69443` has identical Lean sources and passed CI run `45832736228` (Rekor `4127343821`). |
| `docs/faq.md` | `Challenge.lean` said to have 6 `sorry` stubs and 122 lines. | 8 stubs, 143 lines. |

### Errors in the frozen manuscript (`paper/main.tex` and `dist/Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf`, not yet fixed)

| Where | What is wrong | Correction | Affects a theorem statement? |
|---|---|---|---|
| `paper/main.tex:84` (abstract), `:183`, `:803`, `:867`, `:936`; PDF abstract and Corollary 1.2(ii) | Part 5 cited as "Theorem 5.2". | Theorem 3.10 of `arXiv:2611.14735v1`. | Locator in the statement of Corollary 1.2(ii); the formula is unchanged. |
| `paper/main.tex:84` (abstract), `:195`; PDF abstract and Corollary 1.2 | Part 5 cited as "Proposition 6.2" for `C_{1/2}`. | Proposition 4.2. | Locator only. |
| `paper/main.tex:144`; PDF Section 1 | "In Part 5 [Remarks 5.3, 5.5, and 6.3], the conjecture remained open". | Remarks 3.11, 3.13 and 4.3. | No. |
| `paper/main.tex:84`, `:169`, `:175`, `:183`, `:189`; PDF abstract and Corollary 1.2 | The γ coefficients are called "unconditional". | "This removes the one conjectural input from the Banić–Elezović formulas; those formulas still rest on Part 2 Theorem 7.6 and Section 8 and Part 5 Theorem 3.10, which are not formalized." Corollary 1.2 should also say that it uses the `O(ℓ^{-2})` remainder of Part 2 Lemma 7.3, which Lean does not reprove. | Yes: Corollary 1.2 is stated as unconditional; it is conditional on the cited upstream theorems. |
| `paper/main.tex:813`; PDF Section 7 | "the entire proof of Theorem 1.1 and Corollary 1.2(i)–(iii) has been formally verified in Lean 4". | "the proof of Theorem 1.1 and the algebraic identities behind Corollary 1.2(i)–(iii) have been formally verified in Lean 4". This also removes the disagreement with the limitations paragraph at line 936. | No; it narrows the verification claim. |
| `paper/main.tex:841`, `:848`, `:868`; PDF Section 7, Tables 1 and 2 | "730 theorems" described as named and module-private theorems. | 157 author-written theorems and lemmas; 730 theorem constants including 573 compiler-generated auxiliaries. | No. |
| `paper/main.tex:848`; PDF Section 7 | "zero compiler warnings" for a build that includes `Challenge`. | No warnings except the 8 intentional `sorry` warnings of `Challenge.lean`. | No. |
| `paper/main.tex:852`, `:867`, `:868`, `:936`; PDF Sections 7 and 8, Table 2 | "six independent kernels", including "the official C++ kernel" and "leanchecker-paranoid" as separate entries. | Six checker runs; two are the Lean kernel (paranoid and default mode). | No. |
| `paper/main.tex:852`; PDF Section 7 | `Challenge.lean` said to state all eight theorems "verbatim". | Targets 7 and 8 are equal rearrangements; see the README note. | No. |
| `paper/main.tex:936`; PDF Section 8 | Cites "a live negative Lean kernel rejection check in CI" as an inspection aid. | Remove, or cite `adversarial_aTriangle_ne_one_div_32`. | No. |

### Other files not edited in this pass (not yet fixed)

| Where | What is wrong | Correction |
|---|---|---|
| `formalization.yaml:50` | "Theorem 5.2 of Part 5". | Theorem 3.10. |
| `formalization.yaml:27` | "730 exhaustively audited theorems" and "6-kernel comparator targets". | 157 author-written theorems and lemmas (730 audited theorem constants); comparator targets replayed in six checker runs. |
| `CITATION.cff` keywords | "six-kernel verification". | "lake comparator". |
| `blueprint/src/content.tex:117`, `:135` | "Part 5 Thm 5.2"; "6 independent kernels". | Theorem 3.10; six checker runs. |
| `ROADMAP.md:4`, `:6`, `:17` | "unconditional closed forms", "live negative Lean kernel rejection", "Part 5 Theorem 5.2". | As in the README corrections above. |
| `llms-full.txt` | Generated copy of the old wording. | Regenerate from the corrected files. |

`formalization.yaml` and `CITATION.cff` are listed in the SHA-256 manifest `data/MANIFEST.sha256`, which is sealed by RFC 3161 and OpenTimestamps proofs; editing them requires a new manifest and new timestamps, so they are left for the next release.

### Known issues in the formal code (not yet fixed)

None of these changes a theorem statement or a proof; they are docstrings, comments and one CI step.

| Where | What is wrong | Correction |
|---|---|---|
| `lean/Challenge.lean:101,111,120,130`; `lean/Solution.lean:142,154,165,177` | Docstrings call targets 5–8 "Unconditional ... variance coefficient". The theorems are algebraic identities and mention no variance. | "Algebraic identity behind ..." (for example, target 5: the Theorem 7.6 combination after inserting `a_△`; the variance statement itself is cited, not formalized). |
| `lean/Challenge.lean:25,111`; `lean/Solution.lean:154`; `lean/MultinomialTVConjecture/Main.lean:348` | Part 5 cited as "Thm. 5.2" / "Theorem 5.2". | Theorem 3.10. |
| `lean/MultinomialTVConjecture/Main.lean:334` | Theorem 7.6 located at "p. 35". | Printed pp. 59–60. |
| `lean/Challenge.lean:21-25` | Header says all definitions and targets are stated "verbatim". | Targets 7 and 8 are equal rearrangements; say so, or add a one-line lemma equating target 7 with the source's left side `2p_1(3) + 2[b_{N mod 3} − 7/(96π)]`. |
| `lean/MultinomialTVConjecture.lean:17` | Docstring: "18 non-vacuity and adversarial-refutation witnesses". | 20. |
| `lean/VerifyAxioms.lean:34` | Comment: "Primary exported theorems (19 declarations)"; 21 are listed. | 21. |
| `.github/workflows/lean-verify.yml:110-125` | The "negative kernel rejection" step feeds a proof of a different proposition and passes on any non-zero exit, so it cannot fail for a reason that bears on falsity. | Remove it, rename it as an elaboration smoke test, or replace it with a real mutation (change a constant in a copy of `Main.lean` and require `unsolved goals`). |
| Git tag `v2.3.0` | Points to `a1d84d7`, while the archive pins `0a69443` as v2.3.0 (Lean sources identical). | Cut a new release at a current commit; tags are not moved. |

## Withdrawal Policy

If a mathematical flaw or statement-fidelity defect is ever discovered that invalidates a core claim in `CLAIMS.md`, the author commits to logging it here within 72 hours, tagging a corrected release, and posting an explicit retraction/erratum notice on GitHub Releases and any external preprint server where the manuscript has been deposited.
