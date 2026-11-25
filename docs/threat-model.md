# Threat Model (`docs/threat-model.md`)

Because this repository is a mathematical proof and research artifact (no network daemon, no user accounts, no personal data), the primary assets at risk are **epistemic integrity**, **formal soundness**, **bibliographic accuracy**, and **build-chain authenticity**.

## Threat Matrix

| Threat ID | Threat | Impact | Likelihood | Concrete Mitigations |
|---|---|---|---|---|
| **T1** | **Proof soundness bypass** (`sorry`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, `@[extern]`, or meta-level environment tampering) | False mathematical claim presented as Lean-verified | Medium if unchecked | Nested-comment/string-aware forbidden-token lexer in CI; exhaustive `Lean.collectAxioms` metaprogram in `VerifyAxioms.lean`; 6 independent proof kernels via `lake comparator --paranoid` (including Rust `nanoda` and Lean-in-Lean `lean4lean`). |
| **T2** | **Definition drift / vacuous formalization** (Lean proves a trivially true or subtly altered version of Conjecture 7.7) | Formal proof passes kernels but does not prove Banić & Elezović's actual conjecture | Medium | Isolated ~105-line Mathlib-only `lean/Challenge.lean` with verbatim nested multinomial sum; 18 non-vacuity and adversarial false-constant refutation theorems in `NonVacuity.lean`; `docs/statement-fidelity.md` audit table; independent Python exact rational + 80-digit oracle. |
| **T3** | **README / paper claim drift** (human/AI edits manuscript or README without updating verified logs) | Published prose contradicts verified Lean output | Medium | `scripts/check_readme_axioms.py --require-exhaustive` enforces verbatim sync between `README.md` and `results/lean-axioms-all.log`; `scripts/build_blueprint.py` validates every `\lean{...}` symbol against actual Lean files. |
| **T4** | **Citation hallucination or identifier corruption** (e.g., truncated arXiv ID `2610.1336` caught in `E-2026-001`) | Broken or false scholarly attribution | High in AI-assisted writing | `scripts/check_citations.py` static + `--online` DOI/arXiv resolver; regression test permanently guarding `2610.13366`; Crossref retraction check. |
| **T5** | **Supply-chain / CI tampering** (compromised Mathlib cache, Python package, or release artifact) | Malicious code execution or tampered PDF/tarball | Low–Medium | Pinned `lean/lake-manifest.json` commits, pinned `requirements.txt`, `data/MANIFEST.sha256`, release `SHA256SUMS`, Sigstore SLSA `actions/attest-build-provenance@v2`, `gitleaks` secret scan. |
| **T6** | **Path-handling / shell-injection bugs** (e.g., PowerShell wildcard expansion on bracketed paths like `[Vibe Coded (AI)]`) | Broken local builds or misdiagnosed missing files | Medium on Windows | All PowerShell scripts (`Audit-Repo.ps1`) use `-LiteralPath`; Python scripts use `pathlib.Path` and list-form `subprocess.run(..., shell=False)`. |

## Residual Risk

Independent human line-by-line review of `lean/Challenge.lean` against `arXiv:2610.17046v1` remains open (`human_line_by_line_review_recorded: false`). Readers can audit `lean/Challenge.lean` directly in under 5 minutes.
