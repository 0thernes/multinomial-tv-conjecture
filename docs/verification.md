# Verification Stack (`docs/verification.md`)

This repository enforces defense-in-depth verification across **three independent layers**: formal multi-kernel type checking, exact/arbitrary-precision independent computation, and continuous structural/bibliographic integrity checks.

## Layer 1: Lean 4.35.0 Kernel and Comparator Replay

1. **Strict Compiler Hygiene (`lean/lakefile.toml` & Palomar `module` headers):**
   - `autoImplicit = false`, `relaxedAutoImplicit = false`, and `weak.linter.mathlibStandardSet = true` (`weak.linter.style.longLine = false`) enforce Mathlib style hygiene and eliminate accidental free variables in theorem statements.
   - All 10 `.lean` files carry Lean 4.35.0 `module` headers (`public import` + `@[expose] public section`) and REUSE/SPDX Apache-2.0 headers, compiling with no compiler or style-linter warnings except the 8 intentional `declaration uses sorry` warnings of the statement-only `Challenge.lean`.
   - Pinned toolchain `leanprover/lean4:v4.35.0` and pinned Mathlib4/Batteries lockfile (`lean/lake-manifest.json`).
2. **Forbidden-Token Lexer (`.github/workflows/lean-verify.yml`):**
   - Comment- and string-aware nested Lean lexer scans every `.lean` proof file in `lean/MultinomialTVConjecture/` and `lean/Solution.lean` for `sorry`, `admit`, `axiom` (including `public`/`private`/`protected`/`noncomputable`), `partial def`/`theorem`, `native_decide`, `unsafe`, `implemented_by`, and `@[extern]`, and asserts every file carries a `module` header. Zero hits required.
3. **Exhaustive Axiom Audit (`lean/VerifyAxioms.lean`):**
   - Runs `#print axioms` on all 49 exported declarations (21 primary + 20 `NonVacuity` + 8 `ComparatorTarget`) AND a Lean metaprogram (`import all` across all proof modules) iterating `Lean.collectAxioms` over **every** theorem constant (**730 in total**: 157 author-written theorems and lemmas and 573 compiler-generated auxiliaries such as `_proof_N` and `_simp_N`), emitting `ALL_THEOREMS_AXIOM_AUDIT_PASS` only if every theorem lies strictly within `[propext, Classical.choice, Quot.sound]`.
   - `scripts/check_readme_axioms.py --require-exhaustive` verifies that every line of `README.md`'s `#print axioms` excerpt (21 of the 49 lines) and the theorem count match `results/lean-axioms-all.log`.
4. **Comparator (`lake comparator --config comparator.json --paranoid`):**
   - Compares isolated Mathlib-only `lean/Challenge.lean` (8 target stubs, zero proof imports) against sorry-free `lean/Solution.lean` and replays the 8 targets and the declarations they depend on in six checker runs (names as printed in the CI log):
     1. Lean paranoid kernel
     2. `lean4lean` (v4.35.0, Lean-in-Lean kernel)
     3. `nanoda` (0.4.19, Rust kernel)
     4. `con-leche` (v4.35.0)
     5. `con-ron` (v4.35.0)
     6. Lean default kernel
   - Two of the six runs are the Lean kernel. `NonVacuity.lean` is not part of the comparator replay.
5. **Non-Vacuity & Adversarial Checks (`lean/MultinomialTVConjecture/NonVacuity.lean`):**
   - 20 theorems proving concrete exact rational values `hAdj 0..5`, strict sign/ordering bounds (`bRes 0 > 0`, `bRes 1 < 0`, `0 < aTriangle < 1/32`, `d0 < 0`, `gamma2 < 0`), 3 deliberate false-constant refutations (`aTriangle ≠ 1/32`, `d0 ≠ 0`, `¬(bRes 0 = bRes 1 ∧ bRes 1 = bRes 2)`), and concrete `n ∈ {3, 4, 5}` witnesses. Only the 6 `hAdj 0..5` values test a definition directly; the other 14 are corollaries of the proved closed forms.
6. **Batteries Linter (`lake exe runLinter MultinomialTVConjecture`):**
   - Runs report-only in CI and logs to `results/lean-linter.log`.

## Layer 2: Independent Exact Rational & 80-Digit Verification (`scripts/` & `tests/`)

| Test Category (Build Standard) | Implementation |
|---|---|
| **Exact rational oracle (`B12`)** | Exact `fractions.Fraction` 2D multinomial sum vs. 1D `hAdj_mod0..2` formulas (`L = 3..45` in `verify_conjecture.py` and Hypothesis pytest; golden snapshots `L = 0..6`). |
| **Property-based testing (`B10`)** | `hypothesis` strategies verifying exact algebraic invariants, symmetry, non-negativity, and residue-class formulas over generated $L \in [3,45]$ and $n \in [5,500]$. |
| **Negative & adversarial tests (`B06`)** | Verifies false constants (`a_△ = 1/32`, `d_0 = 0`, constant `b_r`), invalid inputs (`n = 0`), and tampered axiom logs are explicitly rejected. The CI step formerly called a live negative Lean kernel test only checks that a proof of a different statement does not elaborate; it passes on any error and does not test falsity. The Lean refutation of `aTriangle = 1/32` is the proved theorem `adversarial_aTriangle_ne_one_div_32`. |
| **Regression tests (`B07`)** | Permanently guards fixed defects `E-2026-001`..`E-2026-011` (citation truncation, `0thernes LLC`, deterministic arXiv bundle + figures + `.bbl`, axiom sync, exact `L = 3..45` & `Theorem 2.3` fidelity parity, Table 1 exact line counts & Claim `C6`, zero local path leaks, 120-dps tail precision, `module` & SPDX headers, dual RFC 3161 `.tsr` + OpenTimestamps `.ots` cryptographic imprint binding). |
| **Golden snapshot tests (`B08`)** | Exact rational table `hAdj(0..6)` and `results/lean-axioms-all.log` theorem count / sentinel checks. |
| **Differential & metamorphic tests (`B11`, `B14`)** | 2D vs. 1D differential agreement; permutation invariance of $(X_1, X_3)$, mod-3 shift relations, linear/cyclic asymptotic coefficient ratios. |
| **Numeric stability (`B20`)** | Cross-precision stability checks across `mp.dps = 50, 80, 120` quantifying catastrophic cancellation in $L(h_{\mathrm{adj}}(L) - c_L L - a_*)$. |
| **Mutation self-check (`B13`)** | Automated mutant-injection tests confirming every sign/coefficient perturbation to `a_△`, `b_0`, `b_1`, `b_2`, `d_0`, `γ_2` is killed by the verifier. |
| **Static analysis & types (`B17`, `B18`)** | `ruff check scripts/ tests/` and `mypy --ignore-missing-imports scripts/` (report-only). |

## Layer 3: Supply-Chain, Citation, Blueprint & Release Integrity

- `scripts/check_citations.py`: Offline static check + optional `--online` HTTPS validation for all DOIs and arXiv IDs in `paper/`. It does not check cited theorem, remark or section numbers.
- `scripts/build_blueprint.py`: Verifies 100% of `\lean{...}` references in `blueprint/src/content.tex` exist at exact line numbers in `lean/`.
- `scripts/generate_manifest.py`: Generates and verifies `data/MANIFEST.sha256` across frozen artifacts and logs.
- `.github/workflows/release.yml`: Produces `SHA256SUMS` and Sigstore SLSA build-provenance attestations (`actions/attest-build-provenance@v2`) on every `v*` tag.
