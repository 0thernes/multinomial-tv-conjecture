/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Sharp Non-Asymptotic Stirling Expansion

Proves the explicit two-sided logarithmic Stirling remainder bound
`1 / (12 n) - 1 / (15 n^3) ≤ R(n) ≤ 1 / (12 n)` for all `n ≥ 1` and derives the quantitative
`O(q^{-3})` central trinomial expansion `p3q_center_expansion` for all `q ≥ 2`.
-/

@[expose] public section

open Real Filter Topology Finset

namespace MultinomialTV

/-- The Stirling log-remainder `stirlingRem n = log(n!) - (n + 1/2) log n + n - (1/2) log(2π)`. -/
noncomputable def stirlingRem (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) - ((n : ℝ) + 1 / 2) * Real.log (n : ℝ) + (n : ℝ) -
    (1 / 2 : ℝ) * Real.log (2 * Real.pi)

/-- Connection to Mathlib's `Stirling.stirlingSeq`:
`stirlingRem n = log (Stirling.stirlingSeq n / √π)` for `n ≥ 1`. -/
lemma stirlingRem_eq_log_stirlingSeq (n : ℕ) (hn : 1 ≤ n) :
    stirlingRem n = Real.log (Stirling.stirlingSeq n / Real.sqrt Real.pi) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2n : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hdiv : (0 : ℝ) < (n : ℝ) / Real.exp 1 := by positivity
  have hseq : Stirling.stirlingSeq n =
      (n.factorial : ℝ) / (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := rfl
  unfold stirlingRem
  rw [hseq, Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_sqrt (by positivity),
    Real.log_pow, Real.log_div (by positivity) (by positivity), Real.log_exp,
    Real.log_mul (by norm_num) (by positivity)]
  ring

/-- `stirlingRem n → 0` as `n → ∞`, directly from Mathlib's Stirling theorem. -/
lemma tendsto_stirlingRem : Tendsto stirlingRem atTop (𝓝 0) := by
  have hseq : Tendsto (fun n => Stirling.stirlingSeq n / Real.sqrt Real.pi) atTop (𝓝 1) := by
    have h := Stirling.tendsto_stirlingSeq_sqrt_pi.div_const (Real.sqrt Real.pi)
    rw [div_self (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))] at h
    exact h
  have hlog : Tendsto (fun n => Real.log (Stirling.stirlingSeq n / Real.sqrt Real.pi)) atTop (𝓝 (Real.log 1)) :=
    (Real.continuousAt_log one_ne_zero).tendsto.comp hseq
  rw [Real.log_one] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (stirlingRem_eq_log_stirlingSeq n hn).symm

/-- One-step telescoping difference of `stirlingRem`:
`stirlingRem n - stirlingRem (n + 1) = (n + 1/2) * log (1 + 1 / n) - 1`. -/
lemma stirlingRem_sub_succ (n : ℕ) (hn : 1 ≤ n) :
    stirlingRem n - stirlingRem (n + 1) =
      ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (n : ℝ)) - 1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have h1 : 1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / (n : ℝ) := by field_simp
  unfold stirlingRem
  have hfac_succ : Real.log (((n + 1).factorial : ℕ) : ℝ) = Real.log ((n : ℝ) + 1) + Real.log (n.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Real.log_mul (by linarith) (by positivity)]
  rw [hfac_succ, h1, Real.log_div (by positivity) (by positivity)]
  push_cast
  ring

/-- Core elementary derivative bound on `[0, 1/2]`:
let `h(x) = (1/2) * log ((1 + x) / (1 - x)) - x - x^3 / (3 * (1 - x^2))`.
Then `-(8/15) * x^5 ≤ h(x) ≤ 0` for all `x ∈ [0, 1/2]`. -/
lemma stirling_aux_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    -(8 / 15 : ℝ) * x ^ 5 ≤
      (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) - x - x ^ 3 / (3 * (1 - x ^ 2)) ∧
    (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) - x - x ^ 3 / (3 * (1 - x ^ 2)) ≤ 0 := by
  let h : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * Real.log ((1 + t) / (1 - t)) - t - t ^ 3 / (3 * (1 - t ^ 2))
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      HasDerivAt h (-(2 * t ^ 4) / (3 * (1 - t ^ 2) ^ 2)) t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 / 2 := ht.2
    have h1pt : 0 < 1 + t := by linarith
    have h1mt : 0 < 1 - t := by linarith
    have h1mt2 : 0 < 1 - t ^ 2 := by nlinarith
    have hlog1 : HasDerivAt (fun u => Real.log (1 + u)) (1 / (1 + t)) t := by
      have h1 : HasDerivAt (fun u => 1 + u) 1 t := (hasDerivAt_id t).const_add 1
      simpa using h1.log (ne_of_gt h1pt)
    have hlog2 : HasDerivAt (fun u => Real.log (1 - u)) (-(1 / (1 - t))) t := by
      have h1 : HasDerivAt (fun u => 1 - u) (-1) t := (hasDerivAt_id t).const_sub 1
      have h2 := h1.log (ne_of_gt h1mt)
      convert h2 using 1; ring
    have hlog_eq : ∀ᶠ u in 𝓝 t,
        (1 / 2 : ℝ) * Real.log ((1 + u) / (1 - u)) =
        (1 / 2 : ℝ) * (Real.log (1 + u) - Real.log (1 - u)) := by
      have hmem : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
      filter_upwards [hmem] with u hu
      rw [Real.log_div (by linarith [hu.1]) (by linarith [hu.2])]
    have hpart1 : HasDerivAt (fun u => (1 / 2 : ℝ) * Real.log ((1 + u) / (1 - u)))
        ((1 / 2 : ℝ) * (1 / (1 + t) - -(1 / (1 - t)))) t := by
      exact ((hlog1.sub hlog2).const_mul (1 / 2 : ℝ)).congr_of_eventuallyEq hlog_eq
    have hnum : HasDerivAt (fun u => u ^ 3) (3 * t ^ 2) t := by
      simpa using hasDerivAt_pow 3 t
    have hden : HasDerivAt (fun u => 3 * (1 - u ^ 2)) (3 * (-(2 * t))) t := by
      have hsq : HasDerivAt (fun u => u ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      exact (hsq.const_sub 1).const_mul 3
    have hquot : HasDerivAt (fun u => u ^ 3 / (3 * (1 - u ^ 2)))
        ((3 * t ^ 2 * (3 * (1 - t ^ 2)) - t ^ 3 * (3 * (-(2 * t)))) / (3 * (1 - t ^ 2)) ^ 2) t :=
      hnum.div hden (ne_of_gt (by positivity))
    have hall := (hpart1.sub (hasDerivAt_id t)).sub hquot
    convert hall using 1
    · ext u; simp [h]
    · field_simp [ne_of_gt h1pt, ne_of_gt h1mt, ne_of_gt h1mt2]; ring
  have hh0 : h 0 = 0 := by simp [h]
  constructor
  · let g : ℝ → ℝ := fun t => h t + (8 / 15 : ℝ) * t ^ 5
    have hmono : MonotoneOn g (Set.Icc 0 (1 / 2)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
      · exact fun t ht => ((hderiv t ht).add
          ((hasDerivAt_pow 5 t).const_mul (8 / 15 : ℝ))).continuousAt.continuousWithinAt
      · exact fun t ht => ((hderiv t (interior_subset ht)).add
          ((hasDerivAt_pow 5 t).const_mul (8 / 15 : ℝ))).differentiableAt.differentiableWithinAt
      · intro t ht
        have hmem : t ∈ Set.Icc (0 : ℝ) (1 / 2) := interior_subset ht
        have hdg : HasDerivAt g (-(2 * t ^ 4) / (3 * (1 - t ^ 2) ^ 2) + (8 / 15 : ℝ) * (5 * t ^ 4)) t := by
          have hd := (hderiv t hmem).add ((hasDerivAt_pow 5 t).const_mul (8 / 15 : ℝ))
          convert hd using 1
        rw [hdg.deriv]
        have ht0 : 0 ≤ t := hmem.1
        have ht1 : t ≤ 1 / 2 := hmem.2
        have h1mt2 : 3 / 4 ≤ 1 - t ^ 2 := by nlinarith
        have hden : 27 / 16 ≤ 3 * (1 - t ^ 2) ^ 2 := by nlinarith
        have hpos_den : 0 < 3 * (1 - t ^ 2) ^ 2 := by linarith
        have hbound : 2 * t ^ 4 / (3 * (1 - t ^ 2) ^ 2) ≤ (8 / 3 : ℝ) * t ^ 4 := by
          rw [div_le_iff₀ hpos_den]
          have ht4 : 0 ≤ t ^ 4 := by positivity
          nlinarith
        rw [neg_div]
        linarith
    have hge := hmono (Set.left_mem_Icc.mpr (by norm_num)) ⟨hx0, hx1⟩ hx0
    simp only [g, h, zero_pow (by norm_num : 5 ≠ 0), mul_zero, add_zero] at hge
    dsimp only [h] at hh0
    linarith
  · have hanti : AntitoneOn h (Set.Icc 0 (1 / 2)) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
      · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
      · exact fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        have hmem : t ∈ Set.Icc (0 : ℝ) (1 / 2) := interior_subset ht
        rw [(hderiv t hmem).deriv]
        have hden : 0 < 3 * (1 - t ^ 2) ^ 2 := by
          have : 0 < 1 - t ^ 2 := by nlinarith [hmem.1, hmem.2]
          positivity
        have hnum : 0 ≤ 2 * t ^ 4 := by positivity
        rw [neg_div]
        linarith [div_nonneg hnum (le_of_lt hden)]
    have hle := hanti (Set.left_mem_Icc.mpr (by norm_num)) ⟨hx0, hx1⟩ hx0
    rw [hh0] at hle
    exact hle

/-- One-step inequality for `stirlingRem n - stirlingRem (n + 1)` vs `1/(12 n) - 1/(12(n+1))`. -/
lemma stirlingRem_step_bounds (n : ℕ) (hn : 1 ≤ n) :
    (1 / (12 * (n : ℝ)) - 1 / (12 * ((n + 1 : ℕ) : ℝ))) -
      (1 / 15 : ℝ) * (1 / (n : ℝ) ^ 3 - 1 / ((n + 1 : ℕ) : ℝ) ^ 3) ≤
      stirlingRem n - stirlingRem (n + 1) ∧
    stirlingRem n - stirlingRem (n + 1) ≤
      1 / (12 * (n : ℝ)) - 1 / (12 * ((n + 1 : ℕ) : ℝ)) := by
  rw [stirlingRem_sub_succ n hn]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set x : ℝ := 1 / (2 * (n : ℝ) + 1)
  have hxpos : 0 < x := by positivity
  have hxle : x ≤ 1 / 2 := by
    dsimp only [x]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h1px : (1 + x) / (1 - x) = 1 + 1 / (n : ℝ) := by
    dsimp only [x]
    have h1 : 2 * (n : ℝ) + 1 ≠ 0 := by linarith
    have h2 : 1 - 1 / (2 * (n : ℝ) + 1) ≠ 0 := by linarith
    field_simp
    ring
  have hident : ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (n : ℝ)) - 1 -
      (1 / (12 * (n : ℝ)) - 1 / (12 * ((n + 1 : ℕ) : ℝ))) =
      ((1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) - x - x ^ 3 / (3 * (1 - x ^ 2))) / x := by
    rw [h1px]
    dsimp only [x]
    have h1 : 2 * (n : ℝ) + 1 ≠ 0 := by linarith
    have h2 : (n : ℝ) ≠ 0 := by linarith
    have h3 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have h4 : (n : ℝ) + 1 ≠ 0 := by linarith
    have h5 : 1 - (1 / (2 * (n : ℝ) + 1)) ^ 2 = (4 * (n : ℝ) * ((n : ℝ) + 1)) / (2 * (n : ℝ) + 1) ^ 2 := by
      field_simp; ring
    rw [h3, h5]
    field_simp
    ring
  obtain ⟨hlb, hub⟩ := stirling_aux_bound (le_of_lt hxpos) hxle
  constructor
  · have hdiv_lb : -(8 / 15 : ℝ) * x ^ 4 ≤
        ((1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) - x - x ^ 3 / (3 * (1 - x ^ 2))) / x := by
      rw [le_div_iff₀ hxpos]
      linarith [show -(8 / 15 : ℝ) * x ^ 4 * x = -(8 / 15 : ℝ) * x ^ 5 by ring]
    have hcmp : (8 / 15 : ℝ) * x ^ 4 ≤
        (1 / 15 : ℝ) * (1 / (n : ℝ) ^ 3 - 1 / ((n + 1 : ℕ) : ℝ) ^ 3) := by
      dsimp only [x]
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hdiff : 1 / (n : ℝ) ^ 3 - 1 / ((n : ℝ) + 1) ^ 3 =
          (3 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 1) / ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 3) := by
        field_simp; ring
      rw [hdiff, one_div_pow]
      have hlhs : (8 / 15 : ℝ) * (1 / (2 * (n : ℝ) + 1) ^ 4) = 8 / (15 * (2 * (n : ℝ) + 1) ^ 4) := by
        field_simp
      have hrhs : (1 / 15 : ℝ) * ((3 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 1) / ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 3)) =
          (3 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 1) / (15 * ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 3)) := by
        field_simp
      rw [hlhs, hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
      have hpoly : (3 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 1) * (15 * (2 * (n : ℝ) + 1) ^ 4) -
          8 * (15 * ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 3)) =
          15 * (40 * (n : ℝ) ^ 6 + 120 * (n : ℝ) ^ 5 + 160 * (n : ℝ) ^ 4 + 120 * (n : ℝ) ^ 3 +
            51 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 1) := by ring
      have hnn : 0 ≤ 15 * (40 * (n : ℝ) ^ 6 + 120 * (n : ℝ) ^ 5 + 160 * (n : ℝ) ^ 4 +
          120 * (n : ℝ) ^ 3 + 51 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 1) := by positivity
      linarith
    linarith
  · have hdiv_ub : ((1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) - x - x ^ 3 / (3 * (1 - x ^ 2))) / x ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hub (le_of_lt hxpos)
    linarith

/-- Explicit non-asymptotic two-sided Stirling log bound for EVERY `n ≥ 1`:
`1/(12 n) - 1/(15 n^3) ≤ stirlingRem n ≤ 1/(12 n)`. -/
theorem stirlingRem_bounds (n : ℕ) (hn : 1 ≤ n) :
    1 / (12 * (n : ℝ)) - 1 / (15 * (n : ℝ) ^ 3) ≤ stirlingRem n ∧
    stirlingRem n ≤ 1 / (12 * (n : ℝ)) := by
  have hfin : ∀ M : ℕ,
      (1 / (12 * (n : ℝ)) - 1 / (12 * ((M + n : ℕ) : ℝ))) -
        (1 / 15 : ℝ) * (1 / (n : ℝ) ^ 3 - 1 / ((M + n : ℕ) : ℝ) ^ 3) ≤
        stirlingRem n - stirlingRem (M + n) ∧
      stirlingRem n - stirlingRem (M + n) ≤
        1 / (12 * (n : ℝ)) - 1 / (12 * ((M + n : ℕ) : ℝ)) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have hstep := stirlingRem_step_bounds (M + n) (by omega)
      have heq : M + n + 1 = M + 1 + n := by omega
      rw [heq] at hstep
      constructor <;> linarith
  have hlim_rem : Tendsto (fun M : ℕ => stirlingRem n - stirlingRem (M + n)) atTop (𝓝 (stirlingRem n)) := by
    have hshift : Tendsto (fun M : ℕ => stirlingRem (M + n)) atTop (𝓝 0) :=
      tendsto_stirlingRem.comp (tendsto_add_atTop_nat n)
    simpa using tendsto_const_nhds.sub hshift
  have hlim_inv1 : Tendsto (fun M : ℕ => 1 / (12 * ((M + n : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℕ => 12 * ((M + n : ℕ) : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 12)
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat n))
    exact tendsto_const_nhds.div_atTop h1
  have hlim_inv3 : Tendsto (fun M : ℕ => 1 / ((M + n : ℕ) : ℝ) ^ 3) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℕ => ((M + n : ℕ) : ℝ) ^ 3) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat n))
    exact tendsto_const_nhds.div_atTop h1
  have hlim_lb : Tendsto (fun M : ℕ =>
      (1 / (12 * (n : ℝ)) - 1 / (12 * ((M + n : ℕ) : ℝ))) -
        (1 / 15 : ℝ) * (1 / (n : ℝ) ^ 3 - 1 / ((M + n : ℕ) : ℝ) ^ 3))
      atTop (𝓝 (1 / (12 * (n : ℝ)) - 1 / (15 * (n : ℝ) ^ 3))) := by
    have h1 : Tendsto (fun M : ℕ => 1 / (12 * (n : ℝ)) - 1 / (12 * ((M + n : ℕ) : ℝ)))
        atTop (𝓝 (1 / (12 * (n : ℝ)) - 0)) := tendsto_const_nhds.sub hlim_inv1
    have h2 : Tendsto (fun M : ℕ => (1 / 15 : ℝ) * (1 / (n : ℝ) ^ 3 - 1 / ((M + n : ℕ) : ℝ) ^ 3))
        atTop (𝓝 ((1 / 15 : ℝ) * (1 / (n : ℝ) ^ 3 - 0))) := (tendsto_const_nhds.sub hlim_inv3).const_mul (1 / 15 : ℝ)
    convert h1.sub h2 using 2
    ring
  have hlim_ub : Tendsto (fun M : ℕ => 1 / (12 * (n : ℝ)) - 1 / (12 * ((M + n : ℕ) : ℝ)))
      atTop (𝓝 (1 / (12 * (n : ℝ)))) := by
    simpa using tendsto_const_nhds.sub hlim_inv1
  constructor
  · exact le_of_tendsto_of_tendsto hlim_lb hlim_rem (Eventually.of_forall fun M => (hfin M).1)
  · exact le_of_tendsto_of_tendsto hlim_rem hlim_ub (Eventually.of_forall fun M => (hfin M).2)

/-- Exact exponential identity for `p_{3q}(q) = (3q)! / (3^(3q) (q!)^3)` using `stirlingRem`. -/
lemma log_p3q_center (q : ℕ) (hq : 1 ≤ q) :
    Real.log (((3 * q).factorial : ℝ) / ((3 : ℝ) ^ (3 * q) * (q.factorial : ℝ) ^ 3)) =
      Real.log (Real.sqrt 3 / (2 * Real.pi * (q : ℝ))) +
        stirlingRem (3 * q) - 3 * stirlingRem q := by
  have hqR : (0 : ℝ) < (q : ℝ) := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h3q : (0 : ℝ) < (3 * q : ℕ) := by positivity
  have hlog3q : Real.log ((3 * q : ℕ) : ℝ) = Real.log 3 + Real.log (q : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)]
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow,
    Real.log_div (by positivity) (by positivity),
    Real.log_sqrt (by norm_num),
    Real.log_mul (by positivity) (by positivity)]
  unfold stirlingRem
  rw [hlog3q]
  push_cast
  ring

/-- Sharp asymptotic expansion of the central trinomial probability `p_{3q}(q)` to `O(q^{-3})`. -/
lemma p3q_center_expansion (q : ℕ) (hq : 2 ≤ q) :
    |((3 * q).factorial : ℝ) / ((3 : ℝ) ^ (3 * q) * (q.factorial : ℝ) ^ 3) -
      (Real.sqrt 3 / (2 * Real.pi * (q : ℝ))) *
        (1 - 2 / (9 * (q : ℝ)) + 2 / (81 * (q : ℝ) ^ 2))| ≤
      (Real.sqrt 3 / (2 * Real.pi * (q : ℝ))) * (1 / (q : ℝ) ^ 3) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq2 : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hq3 : (8 : ℝ) ≤ (q : ℝ) ^ 3 := by nlinarith
  have hpref_pos : 0 < Real.sqrt 3 / (2 * Real.pi * (q : ℝ)) := by positivity
  set P := ((3 * q).factorial : ℝ) / ((3 : ℝ) ^ (3 * q) * (q.factorial : ℝ) ^ 3)
  have hPpos : 0 < P := by positivity
  set δ := stirlingRem (3 * q) - 3 * stirlingRem q
  have hPeq : P = (Real.sqrt 3 / (2 * Real.pi * (q : ℝ))) * Real.exp δ := by
    rw [← Real.exp_log hPpos, log_p3q_center q (by omega)]
    rw [show Real.log (Real.sqrt 3 / (2 * Real.pi * (q : ℝ))) + stirlingRem (3 * q) - 3 * stirlingRem q =
      Real.log (Real.sqrt 3 / (2 * Real.pi * (q : ℝ))) + δ by ring]
    rw [Real.exp_add, Real.exp_log hpref_pos]
  rw [hPeq, ← mul_sub, abs_mul, abs_of_pos hpref_pos]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hpref_pos)
  obtain ⟨hl1, hu1⟩ := stirlingRem_bounds (3 * q) (by omega)
  obtain ⟨hl2, hu2⟩ := stirlingRem_bounds q (by omega)
  have h3q_cast : ((3 * q : ℕ) : ℝ) = 3 * (q : ℝ) := by push_cast; ring
  rw [h3q_cast] at hl1 hu1
  set a : ℝ := -(2 / (9 * (q : ℝ)))
  set e : ℝ := δ - a
  have hδ_sub : 1 / (12 * (3 * (q : ℝ))) - 3 * (1 / (12 * (q : ℝ))) = a := by
    dsimp only [a]; field_simp; ring
  have h405 : 1 / (15 * (3 * (q : ℝ)) ^ 3) = 1 / (405 * (q : ℝ) ^ 3) := by ring
  have h5 : 3 * (1 / (15 * (q : ℝ) ^ 3)) = 1 / (5 * (q : ℝ) ^ 3) := by ring
  have he_lb : -(1 / (405 * (q : ℝ) ^ 3)) ≤ e := by dsimp only [e, δ]; linarith
  have he_ub : e ≤ 1 / (5 * (q : ℝ) ^ 3) := by dsimp only [e, δ]; linarith
  have he_abs : |e| ≤ 1 / (5 * (q : ℝ) ^ 3) := by
    rw [abs_le]
    have h405_le : 1 / (405 * (q : ℝ) ^ 3) ≤ 1 / (5 * (q : ℝ) ^ 3) := by
      gcongr; norm_num
    exact ⟨by linarith, he_ub⟩
  have hδ_abs : |δ| ≤ 1 / (3 * (q : ℝ)) := by
    have hδ_eq : δ = a + e := by dsimp only [e]; ring
    rw [hδ_eq]
    have ha_abs : |a| = 2 / (9 * (q : ℝ)) := by
      dsimp only [a]; rw [abs_neg, abs_of_pos (by positivity)]
    have he_le : 1 / (5 * (q : ℝ) ^ 3) ≤ 1 / (9 * (q : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hsum : 2 / (9 * (q : ℝ)) + 1 / (9 * (q : ℝ)) = 1 / (3 * (q : ℝ)) := by
      field_simp; ring
    exact le_trans (abs_add_le a e) (by linarith)
  have hδ_le1 : |δ| ≤ 1 := by
    refine le_trans hδ_abs ?_
    rw [div_le_one (by positivity)]; linarith
  -- Use Mathlib's Real.exp_bound with n = 3!
  have hexp := Real.exp_bound hδ_le1 (n := 3) (by norm_num)
  have hsum3 : ∑ m ∈ Finset.range 3, δ ^ m / (m.factorial : ℝ) = 1 + δ + δ ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum3] at hexp
  have hcoef3 : |δ| ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) / ((Nat.factorial 3 : ℝ) * (3 : ℕ))) ≤
      1 / (10 * (q : ℝ) ^ 3) := by
    have hpow : |δ| ^ 3 ≤ (1 / (3 * (q : ℝ))) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) hδ_abs 3
    have hnum : (((Nat.succ 3 : ℕ) : ℝ) / ((Nat.factorial 3 : ℝ) * (3 : ℕ))) = 2 / 9 := by
      norm_num [Nat.factorial]
    rw [hnum]
    have hrhs : (1 / (3 * (q : ℝ))) ^ 3 * (2 / 9 : ℝ) = 2 / (243 * (q : ℝ) ^ 3) := by ring
    have hle2 : 2 / (243 * (q : ℝ) ^ 3) ≤ 1 / (10 * (q : ℝ) ^ 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    nlinarith
  have hexp_err : |Real.exp δ - (1 + δ + δ ^ 2 / 2)| ≤ 1 / (10 * (q : ℝ) ^ 3) :=
    le_trans hexp hcoef3
  -- Compare (1 + δ + δ^2/2) with (1 + a + a^2/2) = 1 - 2/(9q) + 2/(81 q^2)
  have htarget : 1 - 2 / (9 * (q : ℝ)) + 2 / (81 * (q : ℝ) ^ 2) = 1 + a + a ^ 2 / 2 := by
    dsimp only [a]; ring
  rw [htarget]
  have hpoly_diff : (1 + δ + δ ^ 2 / 2) - (1 + a + a ^ 2 / 2) = e * (1 + a + e / 2) := by
    have hδ_eq : δ = a + e := by dsimp only [e]; ring
    rw [hδ_eq]; ring
  have hfac_abs : |1 + a + e / 2| ≤ 2 := by
    have ha_le : |a| ≤ 1 / 2 := by
      dsimp only [a]; rw [abs_neg, abs_of_pos (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have he2 : |e / 2| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have : 1 / (5 * (q : ℝ) ^ 3) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      linarith
    exact le_trans (abs_add_le _ _) (by linarith [abs_add_le (1 : ℝ) a, abs_of_pos (by norm_num : (0 : ℝ) < 1)])
  have hpoly_err : |(1 + δ + δ ^ 2 / 2) - (1 + a + a ^ 2 / 2)| ≤ 2 / (5 * (q : ℝ) ^ 3) := by
    rw [hpoly_diff, abs_mul]
    have hmul := mul_le_mul he_abs hfac_abs (abs_nonneg _) (by positivity)
    linarith [show 1 / (5 * (q : ℝ) ^ 3) * 2 = 2 / (5 * (q : ℝ) ^ 3) by ring]
  have hsplit : Real.exp δ - (1 + a + a ^ 2 / 2) =
      (Real.exp δ - (1 + δ + δ ^ 2 / 2)) + ((1 + δ + δ ^ 2 / 2) - (1 + a + a ^ 2 / 2)) := by ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  have hsum_err : 1 / (10 * (q : ℝ) ^ 3) + 2 / (5 * (q : ℝ) ^ 3) = (1 / 2 : ℝ) * (1 / (q : ℝ) ^ 3) := by
    ring
  have hpos3 : 0 ≤ 1 / (q : ℝ) ^ 3 := by positivity
  linarith

end MultinomialTV

end
