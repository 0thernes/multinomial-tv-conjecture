import MultinomialTVConjecture.Main
import Mathlib.Tactic

open scoped BigOperators
open Real Finset

namespace MultinomialTV.NonVacuity

/-!
# Non-Vacuity Witnesses and Adversarial Definition Checks

Establishes that:
1. `hAdj L` reproduces the exact known small-`L` rational expectations for `L = 0, 1, 2, 3, 4, 5`
   computed directly from `Mult(L; 1/3, 1/3, 1/3)`.
2. The proved constants `bRes 0`, `bRes 1`, `bRes 2`, `d0`, `aTriangle`, and `gamma2` satisfy
   nontrivial strict sign/separation inequalities (excluding vacuous or degenerate definitions).
3. Deliberately false constant variants (e.g., `aTriangle = 1 / 32`, `d0 = 0`, `bRes 0 = bRes 1`)
   are provably `False` under our definitions.
4. The hypothesis `n ≠ 0` of `gamma_closed_form` and `gamma_cyclic_closed_form` is concretely
   inhabited at `n = 5`, matching the exact linear and cyclic coefficients.
-/

theorem hAdj_zero : hAdj 0 = 0 := by
  rw [hAdj_eq_nested_sum]
  norm_num [Finset.sum_range_succ]

theorem hAdj_one : hAdj 1 = 1 / 3 := by
  rw [hAdj_eq_nested_sum]
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem hAdj_two : hAdj 2 = 2 / 3 := by
  rw [hAdj_eq_nested_sum]
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem hAdj_three : hAdj 3 = 13 / 9 := by
  rw [hAdj_eq_nested_sum]
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem hAdj_four : hAdj 4 = 140 / 81 := by
  rw [hAdj_eq_nested_sum]
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem hAdj_five : hAdj 5 = 545 / 243 := by
  rw [hAdj_eq_nested_sum]
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem bRes_zero_pos : 0 < bRes 0 := by
  rw [bRes_zero]; positivity

theorem bRes_one_neg : bRes 1 < 0 := by
  rw [bRes_one]
  have h : 0 < 22 * Real.sqrt 3 / (81 * Real.pi) := by positivity
  linarith

theorem bRes_zero_ne_one : bRes 0 ≠ bRes 1 := by
  have h0 := bRes_zero_pos
  have h1 := bRes_one_neg
  linarith

theorem d0_neg : d0 < 0 := by
  rw [conjecture_7_7_d0]
  have h : 0 < 4 * Real.sqrt 3 / (81 * Real.pi) := by positivity
  linarith

theorem aTriangle_lt_one_div_32 : aTriangle < 1 / 32 := by
  rw [conjecture_7_7_aTriangle]
  have h : 0 < 4 * Real.sqrt 3 / 243 := by positivity
  linarith

theorem aTriangle_pos : 0 < aTriangle := by
  rw [conjecture_7_7_aTriangle]
  have hsq : (4 * Real.sqrt 3) ^ 2 < (243 / 32 : ℝ) ^ 2 := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hpos : 0 ≤ 4 * Real.sqrt 3 := by positivity
  have hlt : 4 * Real.sqrt 3 < 243 / 32 := by nlinarith
  linarith

theorem gamma2_neg : gamma2 < 0 := by
  rw [conjecture_7_7_gamma2]
  have h1 : 0 < 1 / (32 * Real.pi) := by positivity
  have h2 : 0 < 8 * Real.sqrt 3 / (243 * Real.pi) := by positivity
  linarith

/-- Adversarial check: the false claim `a_△ = 1/32` (ignoring the non-zero `d_0` contribution) is refuted. -/
theorem adversarial_aTriangle_ne_one_div_32 : aTriangle ≠ 1 / 32 :=
  ne_of_lt aTriangle_lt_one_div_32

/-- Adversarial check: the false claim `d_0 = 0` is refuted. -/
theorem adversarial_d0_ne_zero : d0 ≠ 0 :=
  ne_of_lt d0_neg

/-- Adversarial check: the false claim that all three residue limits coincide is refuted. -/
theorem adversarial_residue_limits_not_constant : ¬ (bRes 0 = bRes 1 ∧ bRes 1 = bRes 2) := by
  intro h; exact bRes_zero_ne_one h.1

/-- Non-vacuity witness at `n = 5` for the linear second-order variance coefficient `γ(5)`. -/
theorem gamma_closed_form_witness_n5 :
    let n : ℝ := 5
    let p1 := (n ^ 2 - 4 * n - 4) / (32 * Real.pi * n)
    let q1 := aTriangle * n / Real.pi - (n + 1) / (8 * Real.pi * n)
    let r1 := -((n + 1) / (8 * Real.pi * n))
    (n - 1) * p1 + 2 * (n - 2) * q1 + (n - 2) * (n - 3) * r1 =
      -(30 / (32 * Real.pi)) - 120 * Real.sqrt 3 / (243 * Real.pi) + 4 / (40 * Real.pi) := by
  have h := gamma_closed_form 5 (by norm_num)
  dsimp only at h ⊢
  rw [h]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp; ring

/-- Non-vacuity witness at `n = 5` for the cyclic second-order variance coefficient `γ_c(5)`. -/
theorem gamma_cyclic_closed_form_witness_n5 :
    let n : ℝ := 5
    let p1 := (n ^ 2 - 4 * n - 4) / (32 * Real.pi * n)
    let q1 := aTriangle * n / Real.pi - (n + 1) / (8 * Real.pi * n)
    let r1 := -((n + 1) / (8 * Real.pi * n))
    n * p1 + 2 * n * q1 + n * (n - 3) * r1 =
      -(45 / (32 * Real.pi)) - 200 * Real.sqrt 3 / (243 * Real.pi) := by
  have h := gamma_cyclic_closed_form 5 (by norm_num)
  dsimp only at h ⊢
  rw [h]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp; ring

end MultinomialTV.NonVacuity
