# Frequently Asked Questions (`docs/faq.md`)

### 1. What exact open problem does this repository solve?
It proves **Conjecture 7.7** (`conj:atriangle`) and the quantitative $O(L^{-2})$ remainder of **Lemma 7.3** of Nikola Banić and Neven Elezović, *Discrete total variation under the multinomial, Part 2: variance under the uniform null* (`arXiv:2610.17046v1`, 2026), establishing exact values for all three residue limits $b_0 = \frac{32\sqrt{3}}{81\pi}$, $b_1 = b_2 = -\frac{22\sqrt{3}}{81\pi}$, the mean $d_0 = -\frac{4\sqrt{3}}{81\pi}$, the triangular constant $a_\triangle = \frac{1}{32} - \frac{4\sqrt{3}}{243}$, and the quadratic coefficient $\gamma_2 = -\frac{1}{32\pi} - \frac{8\sqrt{3}}{243\pi}$, which immediately renders unconditional the formulas for $\gamma(n)$ (Part 2, Thm 7.6) and cyclic $\gamma_c(n)$ (Part 5, `arXiv:2611.14735v1`, Thm 3.10).

### 2. Is this problem listed in the 1,900-problem Unsolved Problems Mega-Atlas?
**No.** Conjecture 7.7 is a specialized 2026 preprint conjecture in discrete probability/asymptotics; it is not one of the 1,900 grand macro open problems in `0thernes/unsolved-problems-mega-atlas`. We explicitly do **not** claim retirement of any Mega-Atlas grand problem.

### 3. Why does `lean/Challenge.lean` contain 9 `sorry` statements?
By design of Lean's `lake comparator` (Palomar-style specification isolation): `Challenge.lean` imports **only Mathlib** (zero files from our proof library) and states the 9 target theorems with `sorry` stubs. `lake comparator --config comparator.json --paranoid` then proves that sorry-free `Solution.lean` exports bit-for-bit identical types to `Challenge.lean` and re-checks the complete proof terms across 6 independent kernels. None of our proof modules (`MultinomialTVConjecture/*`, `Solution.lean`) contain any `sorry`.

### 4. Does Lean 4 prove Banić & Elezović's Theorem 7.6 and Part 5 Theorem 3.10?
**No.** Lean 4 proves Conjecture 7.7 and the quantitative $O(L^{-2})$ Lemma 7.3 remainder unconditionally from first principles (Mathlib), and proves the exact algebraic recombinations `gamma_closed_form`, `gamma_cyclic_closed_form`, `gamma3_closed_form`, and `gamma4_closed_form` given the $(p_1, q_1, r_1)$ linear combinations stated in Part 2 Theorem 7.6 / §7.2 / §8 and Part 5 Theorem 3.10. Those upstream variance decompositions are cited literature results outside our Lean boundary (see [LIMITATIONS.md](../LIMITATIONS.md)).

### 5. Why are there both `LICENSE` (Apache-2.0) and `LICENSE-DOCS` (CC-BY-4.0)?
Following independent scientific publishing best practices (Playbook v1.3 and Mathlib4 upstream compatibility), software and Lean formalizations use **Apache-2.0** (patent grant + clean upstreaming to Mathlib4), while the research manuscript, figures, blueprint, and documentation use **CC-BY-4.0** (attribution-preserving scholarly reuse).

### 6. How can I verify the proof in under a minute without trusting the author?
1. Read `lean/Challenge.lean` (149 lines, Mathlib-only, Lean 4.35.0 `module` header) to confirm the 9 theorem statements match Banić & Elezović (`arXiv:2610.17046v1`).
2. Run `cd lean && lake exe cache get && lake build MultinomialTVConjecture Challenge Solution VerifyAxioms && lake env lean VerifyAxioms.lean`.
3. On Linux with `bubblewrap` (or WSL2/Docker), run `lake comparator --config comparator.json --paranoid`.
