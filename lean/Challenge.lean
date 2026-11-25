/-
Multinomial TV Conjecture (Conjecture 7.7) — Isolated Mathlib-Only Challenge Specification.

This file imports ONLY Mathlib (ZERO imports from our proof library). It defines the exact
multinomial expectation `h_adj(L) = E[|X_2 - X_1| |X_3 - X_2|]` under `Mult(L; 1/3, 1/3, 1/3)`,
the linear/constant terms `c_L`, `a_*`, the residue limits `b_r`, and the derived constants
`d_0`, `a_△`, `γ_2` verbatim from Banić & Elezović (arXiv:2610.17046v1, Sec. 7.2 / Conjecture 7.7;
arXiv:2611.14735v1, Thm. 5.2).

NOTE: Every `sorry` in this file is intentional — `Challenge.lean` is the isolated statement
specification checked against sorry-free `Solution.lean` by
`lake comparator --config comparator.json --paranoid`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas

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

/-- Target 1: Residue class `L ≡ 0 (mod 3)` limit `b_0 = 32√3 / (81π)`. -/
theorem target_tendsto_hAdj_mod0 :
    Tendsto (fun q : ℕ =>
      ((3 * q + 0 : ℕ) : ℝ) * (hAdj (3 * q + 0) - cL * ((3 * q + 0 : ℕ) : ℝ) - aStar))
      atTop (𝓝 (32 * Real.sqrt 3 / (81 * Real.pi))) := by
  sorry

/-- Target 2: Residue class `L ≡ 1 (mod 3)` limit `b_1 = -22√3 / (81π)`. -/
theorem target_tendsto_hAdj_mod1 :
    Tendsto (fun q : ℕ =>
      ((3 * q + 1 : ℕ) : ℝ) * (hAdj (3 * q + 1) - cL * ((3 * q + 1 : ℕ) : ℝ) - aStar))
      atTop (𝓝 (-(22 * Real.sqrt 3 / (81 * Real.pi)))) := by
  sorry

/-- Target 3: Residue class `L ≡ 2 (mod 3)` limit `b_2 = -22√3 / (81π)`. -/
theorem target_tendsto_hAdj_mod2 :
    Tendsto (fun q : ℕ =>
      ((3 * q + 2 : ℕ) : ℝ) * (hAdj (3 * q + 2) - cL * ((3 * q + 2 : ℕ) : ℝ) - aStar))
      atTop (𝓝 (-(22 * Real.sqrt 3 / (81 * Real.pi)))) := by
  sorry

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
  sorry

/-- Target 5: Unconditional linear second-order variance coefficient `γ(n)` (Part 2, Thm. 7.6). -/
theorem target_gamma_closed_form (n : ℝ) (hn : n ≠ 0) :
    let p1 := (n ^ 2 - 4 * n - 4) / (32 * Real.pi * n)
    let q1 := aTriangle * n / Real.pi - (n + 1) / (8 * Real.pi * n)
    let r1 := -((n + 1) / (8 * Real.pi * n))
    (n - 1) * p1 + 2 * (n - 2) * q1 + (n - 2) * (n - 3) * r1 =
      -(n * (n + 1) / (32 * Real.pi)) - 8 * Real.sqrt 3 * n * (n - 2) / (243 * Real.pi) +
        (n - 1) / (8 * Real.pi * n) := by
  sorry

/-- Target 6: Unconditional cyclic second-order variance coefficient `γ_c(n)` (Part 5, Thm. 5.2). -/
theorem target_gamma_cyclic_closed_form (n : ℝ) (hn : n ≠ 0) :
    let p1 := (n ^ 2 - 4 * n - 4) / (32 * Real.pi * n)
    let q1 := aTriangle * n / Real.pi - (n + 1) / (8 * Real.pi * n)
    let r1 := -((n + 1) / (8 * Real.pi * n))
    n * p1 + 2 * n * q1 + n * (n - 3) * r1 =
      -(n * (n + 4) / (32 * Real.pi)) - 8 * Real.sqrt 3 * n ^ 2 / (243 * Real.pi) := by
  sorry

end MultinomialTV.ComparatorTarget
