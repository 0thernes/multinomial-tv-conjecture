# ADR 0001: Exact 2D-to-1D Combinatorial Reduction Instead of Direct 2D Lattice Asymptotics

- **Status:** Accepted
- **Date:** 2026-11-18 (recorded in ADR format 2026-11-25)

## Context

Conjecture 7.7 of Banić & Elezović (`arXiv:2610.17046v1`) asks for the $O(1/L)$ residue limits $b_r = \lim_{q\to\infty}(3q+r)(h_{\mathrm{adj}}(3q+r) - c_L(3q+r) - a_*)$ of a two-dimensional triangular-lattice sum over $(x_1, x_2, x_3)$ with $x_1 + x_2 + x_3 = L$ and integrand $|x_2 - x_1|\,|x_3 - x_2|$. Attacking the 2D corner singularity of $|x_2 - x_1|\,|x_3 - x_2|$ directly via 2D Euler–Maclaurin summation or Edgeworth expansions in Lean 4 would require massive bivariate lattice-point machinery and delicate boundary-layer bookkeeping.

## Decision

Collapse the 2D multinomial sum **algebraically before taking any limits** (`MultinomialTVConjecture/Combinatorial.lean`, theorems `hAdj_mod0`, `hAdj_mod1`, `hAdj_mod2`) into exact rational linear combinations of:
1. The central trinomial probability $p_{3q}(q) = \frac{(3q)!}{3^{3q}(q!)^3}$, and
2. Three 1D weighted sums `sumA q`, `sumB q`, `sumC q`.

Then apply univariate refined Stirling (`StirlingRefined.lean`) and 1D odd-lattice Gaussian Euler–Maclaurin summation (`GaussianEulerMaclaurin.lean`, `LocalAsymptotics.lean`).

## Consequences

- **Positive:** Every 2D combinatorial cancellation is exact and finitary (`ring` / `Finset.sum_bij`), drastically shrinking proof length and making the 1D identities independently checkable in exact rational `Fraction` arithmetic.
- **Positive:** Eliminates all bivariate boundary-layer error analysis; the final residue limits follow by evaluating three explicit continuous polynomials `polyMod0`, `polyMod1`, `polyMod2` at $(0,0,0,0,0)$.
- **Trade-off:** The exact algebraic reductions are tailored to the 3-cell uniform multinomial $(1/3, 1/3, 1/3)$ and would require re-derivation for non-uniform weights.
