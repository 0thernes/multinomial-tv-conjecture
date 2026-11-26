/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
SPDX-FileCopyrightText: 2026 Alexander S. Donahue
SPDX-License-Identifier: Apache-2.0
-/
module

public import MultinomialTVConjecture.Main

/-!
# Sorry-Free Solution Bridge Matched Against `Challenge.lean`

Every definition and theorem signature matches `Challenge.lean` verbatim, uses ZERO `sorry`,
`admit`, `native_decide`, or custom axioms, and is checked across all six Lean 4.35.0 kernels
by `lake comparator --config comparator.json --paranoid`.
-/

@[expose] public section

open scoped BigOperators
open Real Filter Topology Finset

namespace MultinomialTV.ComparatorTarget

/-- Verbatim nested-sum expectation `h_adj(L) = E[|X_2 - X_1| |X_3 - X_2|]`
under `(X_1, X_2, X_3) ~ Mult(L; 1/3, 1/3, 1/3)`. -/
noncomputable def hAdj (L : ℕ) : ℝ :=
  (3 : ℝ)⁻¹ ^ L *
    ∑ x1 ∈ Finset.range (L + 1), ∑ x2 ∈ Finset.range (L - x1 + 1),
      ((L.factorial : ℝ) /
          ((x1.factorial : ℝ) * (x2.factorial : ℝ) * ((L - x1 - x2).factorial : ℝ))) *
        |(x2 : ℝ) - (x1 : ℝ)| * |((L - x1 - x2 : ℕ) : ℝ) - (x2 : ℝ)|

/-- Linear slope `c_L = 2√3 / (3π) + 1/9`. -/
noncomputable def cL : ℝ := 2 * Real.sqrt 3 / (3 * Real.pi) + 1 / 9

/-- Constant offset `a_* = -2√3 / (9π)`. -/
noncomputable def aStar : ℝ := -(2 * Real.sqrt 3 / (9 * Real.pi))

/-- Residue-class `1/L` limit `b_r = lim_{L → ∞, L ≡ r (mod 3)} L (h_adj(L) - c_L L - a_*)`. -/
noncomputable def bRes (r : ℕ) : ℝ :=
  limUnder atTop (fun q : ℕ =>
    ((3 * q + r : ℕ) : ℝ) * (hAdj (3 * q + r) - cL * ((3 * q + r : ℕ) : ℝ) - aStar))

/-- Mean residue constant `d_0 = (b_0 + b_1 + b_2) / 3`. -/
noncomputable def d0 : ℝ := (bRes 0 + bRes 1 + bRes 2) / 3

/-- Adjacent triangular-lattice second-order constant `a_△ = 1/32 + (π/9)(b_0 + b_1 + b_2)`. -/
noncomputable def aTriangle : ℝ := 1 / 32 + Real.pi / 9 * (bRes 0 + bRes 1 + bRes 2)

/-- Leading quadratic coefficient `γ_2 = (64 a_△ - 3) / (32π)` of `γ(n)`. -/
noncomputable def gamma2 : ℝ := (64 * aTriangle - 3) / (32 * Real.pi)

private lemma hAdj_eq_core (L : ℕ) : hAdj L = MultinomialTV.hAdj L :=
  (MultinomialTV.hAdj_eq_nested_sum L).symm

private lemma cL_eq_core : cL = MultinomialTV.cL := rfl
private lemma aStar_eq_core : aStar = MultinomialTV.aStar := rfl

private lemma bRes_eq_core (r : ℕ) : bRes r = MultinomialTV.bRes r := by
  unfold bRes MultinomialTV.bRes
  congr 1
  ext q
  rw [hAdj_eq_core, cL_eq_core, aStar_eq_core]

private lemma d0_eq_core : d0 = MultinomialTV.d0 := by
  unfold d0 MultinomialTV.d0
  rw [bRes_eq_core, bRes_eq_core, bRes_eq_core]

private lemma aTriangle_eq_core : aTriangle = MultinomialTV.aTriangle := by
  unfold aTriangle MultinomialTV.aTriangle
  rw [bRes_eq_core, bRes_eq_core, bRes_eq_core]

private lemma gamma2_eq_core : gamma2 = MultinomialTV.gamma2 := by
  unfold gamma2 MultinomialTV.gamma2
  rw [aTriangle_eq_core]

/-- Target 1: Residue class `L ≡ 0 (mod 3)` limit `b_0 = 32√3 / (81π)`. -/
theorem target_tendsto_hAdj_mod0 :
    Tendsto (fun q : ℕ =>
      ((3 * q + 0 : ℕ) : ℝ) * (hAdj (3 * q + 0) - cL * ((3 * q + 0 : ℕ) : ℝ) - aStar))
      atTop (𝓝 (32 * Real.sqrt 3 / (81 * Real.pi))) := by
  have hfun :
      (fun q : ℕ =>
        ((3 * q + 0 : ℕ) : ℝ) * (hAdj (3 * q + 0) - cL * ((3 * q + 0 : ℕ) : ℝ) - aStar)) =
      (fun q : ℕ =>
        ((3 * q + 0 : ℕ) : ℝ) *
          (MultinomialTV.hAdj (3 * q + 0) - MultinomialTV.cL * ((3 * q + 0 : ℕ) : ℝ) -
            MultinomialTV.aStar)) := by
    ext q; rw [hAdj_eq_core, cL_eq_core, aStar_eq_core]
  rw [hfun]
  exact MultinomialTV.tendsto_hAdj_mod0

/-- Target 2: Residue class `L ≡ 1 (mod 3)` limit `b_1 = -22√3 / (81π)`. -/
theorem target_tendsto_hAdj_mod1 :
    Tendsto (fun q : ℕ =>
      ((3 * q + 1 : ℕ) : ℝ) * (hAdj (3 * q + 1) - cL * ((3 * q + 1 : ℕ) : ℝ) - aStar))
      atTop (𝓝 (-(22 * Real.sqrt 3 / (81 * Real.pi)))) := by
  have hfun :
      (fun q : ℕ =>
        ((3 * q + 1 : ℕ) : ℝ) * (hAdj (3 * q + 1) - cL * ((3 * q + 1 : ℕ) : ℝ) - aStar)) =
      (fun q : ℕ =>
        ((3 * q + 1 : ℕ) : ℝ) *
          (MultinomialTV.hAdj (3 * q + 1) - MultinomialTV.cL * ((3 * q + 1 : ℕ) : ℝ) -
            MultinomialTV.aStar)) := by
    ext q; rw [hAdj_eq_core, cL_eq_core, aStar_eq_core]
  rw [hfun]
  exact MultinomialTV.tendsto_hAdj_mod1

/-- Target 3: Residue class `L ≡ 2 (mod 3)` limit `b_2 = -22√3 / (81π)`. -/
theorem target_tendsto_hAdj_mod2 :
    Tendsto (fun q : ℕ =>
      ((3 * q + 2 : ℕ) : ℝ) * (hAdj (3 * q + 2) - cL * ((3 * q + 2 : ℕ) : ℝ) - aStar))
      atTop (𝓝 (-(22 * Real.sqrt 3 / (81 * Real.pi)))) := by
  have hfun :
      (fun q : ℕ =>
        ((3 * q + 2 : ℕ) : ℝ) * (hAdj (3 * q + 2) - cL * ((3 * q + 2 : ℕ) : ℝ) - aStar)) =
      (fun q : ℕ =>
        ((3 * q + 2 : ℕ) : ℝ) *
          (MultinomialTV.hAdj (3 * q + 2) - MultinomialTV.cL * ((3 * q + 2 : ℕ) : ℝ) -
            MultinomialTV.aStar)) := by
    ext q; rw [hAdj_eq_core, cL_eq_core, aStar_eq_core]
  rw [hfun]
  exact MultinomialTV.tendsto_hAdj_mod2

/-- Target 4: Complete resolution of Conjecture 7.7 (`conj:atriangle`, arXiv:2610.17046v1). -/
theorem target_conjecture_7_7 :
    aTriangle = 1 / 32 - 4 * Real.sqrt 3 / 243 ∧
    gamma2 = -(1 / (32 * Real.pi)) - 8 * Real.sqrt 3 / (243 * Real.pi) ∧
    d0 = -(4 * Real.sqrt 3 / (81 * Real.pi)) ∧
    bRes 0 = 32 * Real.sqrt 3 / (81 * Real.pi) ∧
    bRes 1 = -(22 * Real.sqrt 3 / (81 * Real.pi)) ∧
    bRes 2 = -(22 * Real.sqrt 3 / (81 * Real.pi)) ∧
    (∀ r ∈ ({0, 1, 2} : Finset ℕ),
      bRes r = d0 + 4 * Real.sqrt 3 / (9 * Real.pi) * Real.cos (2 * Real.pi * (r : ℝ) / 3)) := by
  rw [aTriangle_eq_core, gamma2_eq_core, d0_eq_core]
  simp only [bRes_eq_core]
  exact MultinomialTV.conjecture_7_7

/-- Target 5: Unconditional linear second-order variance coefficient `γ(n)` (Part 2, Thm. 7.6). -/
theorem target_gamma_closed_form (n : ℝ) (hn : n ≠ 0) :
    let p1 := (n ^ 2 - 4 * n - 4) / (32 * Real.pi * n)
    let q1 := aTriangle * n / Real.pi - (n + 1) / (8 * Real.pi * n)
    let r1 := -((n + 1) / (8 * Real.pi * n))
    (n - 1) * p1 + 2 * (n - 2) * q1 + (n - 2) * (n - 3) * r1 =
      -(n * (n + 1) / (32 * Real.pi)) - 8 * Real.sqrt 3 * n * (n - 2) / (243 * Real.pi) +
        (n - 1) / (8 * Real.pi * n) := by
  dsimp only
  rw [aTriangle_eq_core]
  exact MultinomialTV.gamma_closed_form n hn

/-- Target 6: Unconditional cyclic second-order variance coefficient `γ_c(n)` (Part 5, Thm. 5.2). -/
theorem target_gamma_cyclic_closed_form (n : ℝ) (hn : n ≠ 0) :
    let p1 := (n ^ 2 - 4 * n - 4) / (32 * Real.pi * n)
    let q1 := aTriangle * n / Real.pi - (n + 1) / (8 * Real.pi * n)
    let r1 := -((n + 1) / (8 * Real.pi * n))
    n * p1 + 2 * n * q1 + n * (n - 3) * r1 =
      -(n * (n + 4) / (32 * Real.pi)) - 8 * Real.sqrt 3 * n ^ 2 / (243 * Real.pi) := by
  dsimp only
  rw [aTriangle_eq_core]
  exact MultinomialTV.gamma_cyclic_closed_form n hn

end MultinomialTV.ComparatorTarget

end
