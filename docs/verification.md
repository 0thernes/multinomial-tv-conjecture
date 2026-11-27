# Verification Stack (`docs/verification.md`)

This repository enforces defense-in-depth verification across **three independent layers**: formal Lean 4 kernel checking plus comparator replay, exact/arbitrary-precision independent computation with isolated code-mutation auditing, and continuous structural/bibliographic integrity checks.

## Layer 1: Lean 4.35.0 Kernel and Comparator Replay

1. **Strict Compiler Hygiene (`lean/lakefile.toml` & Palomar `module` headers):**
   - `autoImplicit = false`, `relaxedAutoImplicit = false`, and `weak.linter.mathlibStandardSet = true` (`weak.linter.style.longLine = false`) enforce Mathlib style hygiene and eliminate accidental free variables in theorem statements.
   - All 10 `.lean` files carry Lean 4.35.0 `module` headers (`public import` + `@[expose] public section`) and REUSE/SPDX Apache-2.0 headers, compiling with no compiler or style-linter warnings except the 9 intentional `declaration uses sorry` warnings of the statement-only `Challenge.lean`.
   - Pinned toolchain `leanprover/lean4:v4.35.0` and pinned Mathlib4/Batteries lockfile (`lean/lake-manifest.json`).
2. **Forbidden-Token Lexer (`.github/workflows/lean-verify.yml`):**
   - Comment- and string-aware nested Lean lexer scans every `.lean` proof file in `lean/MultinomialTVConjecture/` and `lean/Solution.lean` for `sorry`, `admit`, `axiom` (including `public`/`private`/`protected`/`noncomputable`), `partial def`/`theorem`, `native_decide`, `unsafe`, `implemented_by`, and `@[extern]`, and asserts every file carries a `module` header. Zero hits required.
3. **Exhaustive Axiom Audit (`lean/VerifyAxioms.lean`):**
   - Runs `#print axioms` on all 55 exported declarations (26 primary + 20 `NonVacuity` + 9 `ComparatorTarget`) AND a Lean metaprogram (`import all` across all proof modules) iterating `Lean.collectAxioms` over **every** theorem constant (**892 in total**: **187** author-written theorems and lemmas and **705** compiler-generated auxiliaries such as `_proof_N` and `_simp_N`), emitting `ALL_THEOREMS_AXIOM_AUDIT_PASS` only if every theorem lies strictly within `[propext, Classical.choice, Quot.sound]`.
   - `scripts/check_readme_axioms.py --require-exhaustive` verifies that every line of `README.md`'s `#print axioms` excerpt (23 of the 55 lines) and the theorem count match `results/lean-axioms-all.log`.
4. **Comparator (`lake comparator --config comparator.json --paranoid`):**
   - Compares isolated Mathlib-only `lean/Challenge.lean` (9 target stubs including `target_lemma_7_3_O_inv_sq`, zero proof imports) against sorry-free `lean/Solution.lean` and replays all 9 targets and the declarations they depend on in **six checker runs** (names as printed in the CI log):
     1. Lean paranoid kernel
     2. `lean4lean` (v4.35.0, Lean-in-Lean kernel)
     3. `nanoda` (0.4.19, Rust kernel)
     4. `con-leche` (v4.35.0)
     5. `con-ron` (v4.35.0)
     6. Lean default kernel
   - Two of the six runs are the Lean kernel. `NonVacuity.lean` is not part of the comparator replay.
5. **Non-Vacuity & Adversarial Checks (`lean/MultinomialTVConjecture/NonVacuity.lean`):**
   - 20 theorems proving concrete exact rational values `hAdj 0..5`, strict sign/ordering bounds (`bRes 0 > 0`, `bRes 1 < 0`, `0 < aTriangle < 1/32`, `d0 < 0`, `gamma2 < 0`), 3 deliberate false-constant refutations (`aTriangle ≠ 1/32`, `d0 ≠ 0`, `¬(bRes 0 = bRes 1 ∧ bRes 1 = bRes 2)`), and concrete `n ∈ {3, 4, 5}` witnesses. Only the **6** `hAdj 0..5` values test a definition directly; the other **14** are corollaries/refutations of the proved closed forms.
6. **Batteries Linter (`lake exe runLinter MultinomialTVConjecture`):**
   - Runs report-only in CI and logs to `results/lean-linter.log`.

## Layer 2: Independent Exact Rational & 80-Digit Verification (`scripts/` & `tests/`)

| Test Category (Build Standard) | Implementation |
|---|---|
| **Exact rational oracle (`B12`)** | Exact `fractions.Fraction` 2D multinomial sum vs. 1D `hAdj_mod0..2` formulas (`L = 3..45` in `verify_conjecture.py` and Hypothesis pytest; golden snapshots `L = 0..6`). |
| **Property-based testing (`B10`)** | `hypothesis` strategies verifying exact algebraic invariants, $S_3$ pointwise identity (1,000 cases), consecutive-ratio Gaussian tail bounds (1,000 cases), linear/cyclic $\gamma$ identities (1,000 cases), and 2D==1D rational reduction over $L \in [3,45]$ (>3,000 total cases). |
| **Negative & adversarial tests (`B06`)** | Verifies false constants (`a_△ = 1/32`, `d_0 = 0`, constant `b_r`), invalid inputs (`n = 0`), tampered axiom logs, tampered `.tsr`/`.ots`/manifest digests, and broken citation parity are explicitly rejected. In Lean, the mathematical refutation of `aTriangle = 1/32` is the proved theorem `adversarial_aTriangle_ne_one_div_32`; CI also runs a mutated-constant elaboration smoke test requiring `unsolved goals`. |
| **Regression tests (`B07`)** | Permanently guards fixed defects `E-2026-001`..`E-2026-018` (citation truncation, `0thernes LLC`, deterministic arXiv bundle + figures + `.bbl`, axiom sync, exact `L = 3..45` & `Theorem 2.3` fidelity parity, Table 1 exact line counts & Claim `C6`, zero local path leaks, 120-dps tail precision, `module` & SPDX headers, dual RFC 3161 `.tsr` + OpenTimestamps `.ots` cryptographic imprint binding, Part 5 `Theorem 3.10`/`Proposition 4.2`/`math.PR` primary-source citation accuracy, 9-target comparator + 20-mutant report parity, and zero overclaimed kernel/conflict strings). |
| **Golden snapshot tests (`B08`)** | Exact rational table `hAdj(0..6)` and `results/lean-axioms-all.log` theorem count / sentinel checks. |
| **Differential & metamorphic tests (`B11`, `B14`)** | 2D vs. 1D exact rational differential check + 1,140-input differential oracle (`p3q_exact` vs independent `mpmath.loggamma`); permutation invariance of $(X_1, X_3)$, mod-3 shift relations, linear/cyclic asymptotic coefficient ratios. |
| **Numeric stability (`B20`)** | Cross-precision stability checks across `mp.dps = 50, 80, 120` quantifying catastrophic cancellation in $L(h_{\mathrm{adj}}(L) - c_L L - a_*)$, plus empirical $O(L^{-2})$ boundedness of $L(b_r(L)-b_r)$. |
| **Code mutation audit (`B13`)** | Isolated AST-validated source mutation runner `scripts/run_mutation_audit.py` injecting 20 semantic code mutants across 6 core verification scripts (`verify_conjecture.py`, `check_readme_axioms.py`, `check_citations.py`, `build_arxiv_bundle.py`, `stamp_timestamps.py`, `generate_manifest.py`) behind a mandatory unmutated baseline PASS gate (`results/mutation-report.json`: 20/20 killed, 100.0%), plus constant-perturbation tests. |
| **Static analysis & types (`B17`, `B18`)** | `ruff check scripts/ tests/` and `mypy --ignore-missing-imports scripts/ tests/` (report-only). |

## Layer 3: Supply-Chain, Citation, Blueprint & Release Integrity

- `scripts/check_citations.py`: Offline static check + optional `--online` HTTPS validation for all DOIs and arXiv IDs in `paper/`. It does not check cited theorem, remark, or section numbers (those are audited by hand against the live arXiv sources).
- `scripts/build_blueprint.py`: Verifies 100% of `\lean{...}` references in `blueprint/src/content.tex` exist at exact line numbers in `lean/`.
- `scripts/generate_manifest.py`: Generates and verifies `data/MANIFEST.sha256` (31 LF-deterministic entries) across frozen artifacts and logs.
- `.github/workflows/release.yml`: Produces `SHA256SUMS` and Sigstore SLSA build-provenance attestations (`actions/attest-build-provenance@v2`) on every `v*` tag.
