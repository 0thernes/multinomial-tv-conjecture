/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public import MultinomialTVConjecture.Main
import Mathlib.Tactic

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

@[expose] public section

open scoped BigOperators
open Real Finset

namespace MultinomialTV.NonVacuity

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

/-- Non-vacuity witness at `N = 0` for the degenerate `n = 3` formula `γ(3; 0)`. -/
theorem gamma3_closed_form_witness_N0 :
    let n : ℝ := 3
    let p1 := (n ^ 2 - 4 * n - 4) / (32 * Real.pi * n)
    let q1 := aTriangle * n / Real.pi - (n + 1) / (8 * Real.pi * n)
    2 * p1 + 2 * q1 + 2 * (bRes 0 - d0) =
      -(7 / (24 * Real.pi)) + 64 * Real.sqrt 3 / (81 * Real.pi) := by
  have h := gamma3_closed_form 0
  dsimp only at h ⊢
  simp only [Nat.zero_mod, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero, mul_one] at h
  rw [h]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp; ring

/-- Non-vacuity witness at `N = 0` for the degenerate `n = 4` formula `γ(4; 0)`. -/
theorem gamma4_closed_form_witness_N0 :
    let n : ℝ := 4
    let p1 := (n ^ 2 - 4 * n - 4) / (32 * Real.pi * n)
    let q1 := aTriangle * n / Real.pi - (n + 1) / (8 * Real.pi * n)
    let r1 := -((n + 1) / (8 * Real.pi * n))
    3 * p1 + 4 * q1 + 2 * r1 + 1 / (2 * Real.pi) =
      -(1 / (32 * Real.pi)) - 64 * Real.sqrt 3 / (243 * Real.pi) := by
  have h := gamma4_closed_form 0
  dsimp only at h ⊢
  simp only [pow_zero] at h
  rw [h]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp; ring

/-- Adversarial check: the `O(L^{-2})` remainder bound of `lemma_7_3_O_inv_sq` (Target 9) is
non-degenerate (no zero constant `C = 0` suffices, because at `L = 1` the remainder is strictly
positive: `2/9 - 14√3/(81π) > 0`). -/
theorem adversarial_lemma_7_3_zero_const_false :
    ¬ (∀ L : ℕ, 1 ≤ L →
      |hAdj L - cL * (L : ℝ) - aStar - bRes (L % 3) / (L : ℝ)| ≤ 0 / (L : ℝ) ^ 2) := by
  intro h
  have h1 := h 1 le_rfl
  simp only [Nat.cast_one, mul_one, div_one, zero_div, Nat.one_mod] at h1
  have hzero : hAdj 1 - cL - aStar - bRes 1 = 0 := abs_nonpos_iff.mp h1
  rw [hAdj_one, bRes_one] at hzero
  unfold cL aStar at hzero
  have hpi_ge : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsqrt_lt : Real.sqrt 3 < 2 := by
    have hsq : Real.sqrt 3 ^ 2 < (2 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg 3]
  have hsimp :
      (1 / 3 : ℝ) - (2 * Real.sqrt 3 / (3 * Real.pi) + 1 / 9) -
        (-(2 * Real.sqrt 3 / (9 * Real.pi))) - (-(22 * Real.sqrt 3 / (81 * Real.pi))) =
      (18 * Real.pi - 14 * Real.sqrt 3) / (81 * Real.pi) := by
    have hpi : Real.pi ≠ 0 := ne_of_gt hpi_pos
    field_simp; ring
  rw [hsimp] at hzero
  have hnum_pos : 0 < 18 * Real.pi - 14 * Real.sqrt 3 := by nlinarith
  have hfrac_pos : 0 < (18 * Real.pi - 14 * Real.sqrt 3) / (81 * Real.pi) := by positivity
  linarith

/-- Non-vacuity witness at `N = 1` (non-zero residue class `1 mod 3`) for the literal
Part 2 §7.2 `n = 3` source expression and bridge `q_1(3) - d_0 = -7/(96π)` (Target 10). -/
theorem gamma3_source_form_witness_N1 :
    let n : ℝ := 3
    let p1 := (n ^ 2 - 4 * n - 4) / (32 * Real.pi * n)
    let q1 := aTriangle * n / Real.pi - (n + 1) / (8 * Real.pi * n)
    (q1 - d0 = -(7 / (96 * Real.pi))) ∧
      (2 * p1 + 2 * (bRes 1 - 7 / (96 * Real.pi)) =
        -(7 / (24 * Real.pi)) - 44 * Real.sqrt 3 / (81 * Real.pi)) := by
  have h := gamma3_source_form 1
  dsimp only at h ⊢
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  simp only [Nat.one_mod, Nat.cast_one, mul_one] at h2
  rw [h2]
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    have hEq : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
    rw [hEq, Real.cos_pi_sub, Real.cos_pi_div_three]
  rw [hcos]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp; ring

end MultinomialTV.NonVacuity

end
