# Proof & Verification Architecture (`docs/architecture.md`)

## Mathematical Proof Pipeline

The Lean 4 formalization proves Conjecture 7.7 and the quantitative $O(L^{-2})$ remainder of Lemma 7.3 of Banić & Elezović (`arXiv:2610.17046v1`, an unrefereed arXiv v1 preprint) through a five-stage reduction that replaces an intractable 2D triangular-lattice asymptotic expansion with three elementary 1D sums:

```mermaid
flowchart TD
    A["Combinatorial.lean<br/>2D Simplex -> Exact 1D Sums (hAdj_mod0..2)"] --> E["Main.lean<br/>Poly Combination + tendsto_hAdj_mod0..2 + lemma_7_3_O_inv_sq"]
    B["StirlingRefined.lean<br/>Central Trinomial Expansion p3q_center_expansion"] --> E
    C["GaussianEulerMaclaurin.lean<br/>Odd Gaussian Sums (O(h^3) & O(h^4))"] --> D["LocalAsymptotics.lean<br/>1D Asymptotics tendsto_sumA..C & sumA..C_O_inv_sq"]
    B --> D
    D --> E
    E --> F["Conjecture 7.7 + Lemma 7.3 O(L^-2) + gamma algebraic identities"]
    F --> G["NonVacuity.lean<br/>22 Concrete & Adversarial Witnesses (leanchecker)"]
    F --> H["Solution.lean vs Challenge.lean<br/>lake comparator --paranoid, six checker runs (10 Targets)"]
```

## Module Breakdown

| Module | Role | Key Exports |
|---|---|---|
| `lean/MultinomialTVConjecture/Combinatorial.lean` | Exact simplex summation and algebraic identities eliminating the 2D sum | `hAdj`, `p3q`, `sumA`, `sumB`, `sumC`, `hAdj_mod0`, `hAdj_mod1`, `hAdj_mod2` |
| `lean/MultinomialTVConjecture/StirlingRefined.lean` | Quantitative Robbins-type Stirling remainder with $O(q^{-3})$ control | `p3q_center_expansion` |
| `lean/MultinomialTVConjecture/GaussianEulerMaclaurin.lean` | 3rd- and 4th-order Euler–Maclaurin approximations of odd-lattice Gaussian sums | `oddGauss_sum_approx`, `oddGauss_sum_approx_order4` |
| `lean/MultinomialTVConjecture/LocalAsymptotics.lean` | Local Gaussian/Laplace $o(q^{-1})$ limits and $O(q^{-2})$ remainder bounds for the three 1D sums (0 `@[nolint]`) | `tendsto_sumA..C`, `sumA_O_inv_sq`, `sumB_O_inv_sq`, `sumC_O_inv_sq` |
| `lean/MultinomialTVConjecture/Main.lean` | Exact nested-sum equivalence, residue limits `b_0, b_1, b_2`, quantitative $O(L^{-2})$ Lemma 7.3, Conjecture 7.7, and linear/cyclic/small-bin algebraic identities (incl. literal Part 2 §7.2 `gamma3_source_form`) | `hAdj_eq_nested_sum`, `tendsto_hAdj_mod0..2`, `lemma_7_3_O_inv_sq`, `conjecture_7_7`, `gamma_closed_form`, `gamma_cyclic_closed_form`, `gamma3_closed_form`, `gamma3_source_form`, `gamma4_closed_form` |
| `lean/MultinomialTVConjecture/NonVacuity.lean` | 6 direct definition checks (`hAdj 0..5`) + 16 sign, witness, and false-constant/non-degeneracy refutation corollaries covering all 10 targets (independently replayed via `leanchecker`) | `hAdj_zero..five`, `adversarial_*`, `gamma*_witness_*` |
| `lean/Challenge.lean` | 100% Mathlib-only target statements (164 lines, 10 intentional `sorry` stubs, zero proof-library imports) | `MultinomialTV.ComparatorTarget.target_*` |
| `lean/Solution.lean` | Sorry-free bridge proving `Challenge.lean` targets via `MultinomialTVConjecture.Main` | Same 10 declarations, replayed in six comparator checker runs |
| `lean/VerifyAxioms.lean` | Exhaustive `Lean.collectAxioms` metaprogram + 59 explicit `#print axioms` checks | Emits `ALL_THEOREMS_AXIOM_AUDIT_PASS` (`896` theorem constants [`191` author + `705` auxiliaries] + `65` definitions) |

## Independent Verification Layer

- **`scripts/verify_conjecture.py`**: Completely independent Python implementation computing exact rational `Fraction` values for $L=3..45$ (0/1 error) and 80-digit `mpmath` evaluations up to $q=3{,}000$ ($L=9{,}001$) with 28-point Neville–Richardson extrapolation matching all 6 constants to $>54$ decimal digits ($<3\times 10^{-55}$).
- **`tests/` & `scripts/run_mutation_audit.py`**: Automated `pytest` + `hypothesis` ladder testing exact identities, negative/adversarial bounds, regressions, golden snapshots, differential/oracle checks, metamorphic invariants, multi-precision stability, isolated AST source-code mutation auditing (`24/24` killed across 7 scripts), and repository metadata integrity.
- **`blueprint/` & `scripts/build_blueprint.py`**: Validates every `\lean{...}` tag in `blueprint/src/content.tex` against actual Lean declarations and emits a static SVG DAG + HTML page at `build/site/blueprint/`.
