# Verification Stack (`docs/verification.md`)

This repository enforces defense-in-depth verification across **three independent layers**: formal multi-kernel type checking, exact/arbitrary-precision independent computation, and continuous structural/bibliographic integrity checks.

## Layer 1: Lean 4.35.0 & 6 Independent Proof Kernels

1. **Strict Compiler Hygiene (`lean/lakefile.toml`):**
   - `autoImplicit = false` and `relaxedAutoImplicit = false` eliminate accidental free variables in theorem statements.
   - Pinned toolchain `leanprover/lean4:v4.35.0` and pinned Mathlib4/Batteries lockfile (`lean/lake-manifest.json`).
2. **Forbidden-Token Lexer (`.github/workflows/lean-verify.yml`):**
   - Comment- and string-aware nested Lean lexer scans every `.lean` proof file in `lean/MultinomialTVConjecture/` and `lean/Solution.lean` for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, and `@[extern]`. Zero hits required.
3. **Exhaustive Axiom Audit (`lean/VerifyAxioms.lean`):**
   - Runs `#print axioms` on all 43 exported declarations (19 primary + 18 `NonVacuity` + 6 `ComparatorTarget`) AND a Lean metaprogram iterating `Lean.collectAxioms` over **every** theorem under namespace `MultinomialTV`, emitting `ALL_THEOREMS_AXIOM_AUDIT_PASS` only if every theorem lies strictly within `[propext, Classical.choice, Quot.sound]`.
   - `scripts/check_readme_axioms.py --require-exhaustive` verifies that `README.md`'s verbatim `#print axioms` block matches `results/lean-axioms-all.log` line-for-line.
4. **Six-Kernel Comparator (`lake comparator --config comparator.json --paranoid`):**
   - Compares isolated Mathlib-only `lean/Challenge.lean` (6 target stubs, zero proof imports) against sorry-free `lean/Solution.lean` across all 6 independent type-checkers shipped in Lean 4.35.0:
     1. Official Lean 4.35.0 C++ kernel
     2. `leanchecker-paranoid` (v4.35.0)
     3. `lean4lean` (v4.35.0, Lean-in-Lean kernel)
     4. `nanoda` (0.4.19, Rust kernel)
     5. `con-leche` (v4.35.0)
     6. `con-ron` (v4.35.0)
5. **Non-Vacuity & Adversarial Checks (`lean/MultinomialTVConjecture/NonVacuity.lean`):**
   - 18 theorems proving concrete exact rational values `hAdj 0..5`, strict sign/ordering bounds (`bRes 0 > 0`, `bRes 1 < 0`, `0 < aTriangle < 1/32`, `d0 < 0`, `gamma2 < 0`), 3 deliberate false-constant refutations (`aTriangle ≠ 1/32`, `d0 ≠ 0`, `¬(bRes 0 = bRes 1 ∧ bRes 1 = bRes 2)`), and concrete `n = 5` witnesses.
6. **Batteries Linter (`lake exe runLinter MultinomialTVConjecture`):**
   - Runs report-only in CI and logs to `results/lean-linter.log`.

## Layer 2: Independent Exact Rational & 80-Digit Verification (`scripts/` & `tests/`)

| Test Category (Build Standard) | Implementation |
|---|---|
| **Exact rational oracle (`B12`)** | Exact `fractions.Fraction` 2D multinomial sum vs. 1D `hAdj_mod0..2` formulas (`L = 3..45` in `verify_conjecture.py`, `L = 0..45` in pytest). |
| **Property-based testing (`B10`)** | `hypothesis` strategies verifying exact algebraic invariants, symmetry, non-negativity, and residue-class formulas over generated $L, n$. |
| **Negative & adversarial tests (`B06`)** | Verifies false constants (`a_△ = 1/32`, `d_0 = 0`, constant `b_r`), invalid inputs (`n = 0`), and tampered axiom logs are explicitly rejected. |
| **Regression tests (`B07`)** | Permanently guards fixed defects `E-2026-001` (`2610.1336` truncation), `E-2026-002` (`0thernes LLC`), `E-2026-003` (`00README.XXX` + reproducible tar), `E-2026-004` (axiom-sync). |
| **Golden snapshot tests (`B08`)** | Exact rational table `hAdj(0..6)` and `results/lean-axioms-all.log` theorem count / sentinel checks. |
| **Differential & metamorphic tests (`B11`, `B14`)** | 2D vs. 1D differential agreement; permutation invariance of $(X_1, X_3)$, mod-3 shift relations, linear/cyclic asymptotic coefficient ratios. |
| **Numeric stability (`B20`)** | Cross-precision stability checks across `mp.dps = 50, 80, 120` quantifying catastrophic cancellation in $L(h_{\mathrm{adj}}(L) - c_L L - a_*)$. |
| **Mutation self-check (`B13`)** | Automated mutant-injection tests confirming every sign/coefficient perturbation to `a_△`, `b_0`, `b_1`, `b_2`, `d_0`, `γ_2` is killed by the verifier. |
| **Static analysis & types (`B17`, `B18`)** | `ruff check scripts/ tests/` and `mypy --ignore-missing-imports scripts/` (report-only). |

## Layer 3: Supply-Chain, Citation, Blueprint & Release Integrity

- `scripts/check_citations.py`: Offline static check + optional `--online` HTTPS validation for all DOIs and arXiv IDs in `paper/`.
- `scripts/build_blueprint.py`: Verifies 100% of `\lean{...}` references in `blueprint/src/content.tex` exist at exact line numbers in `lean/`.
- `scripts/generate_manifest.py`: Generates and verifies `data/MANIFEST.sha256` across frozen artifacts and logs.
- `.github/workflows/release.yml`: Produces `SHA256SUMS` and Sigstore SLSA build-provenance attestations (`actions/attest-build-provenance@v2`) on every `v*` tag.
