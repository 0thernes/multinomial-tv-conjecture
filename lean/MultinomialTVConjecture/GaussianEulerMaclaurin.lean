/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
SPDX-FileCopyrightText: 2026 Alexander S. Donahue
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Cubic Euler-Maclaurin Summation for Odd-Gaussian Moments

Establishes the exact elementary antiderivative and self-contained third-order Euler-Maclaurin
approximation `oddGauss_sum_approx` for odd-Gaussian lattice sums `g_j(t) = t^{2j+1} exp(-3 t^2)`,
capturing the exact `-h^2 / 12` Bernoulli shift at `j = 0`.
-/

@[expose] public section

open scoped BigOperators
open Real Filter Topology Finset intervalIntegral

namespace MultinomialTV

/-! ### Part 1: Elementary exponential domination lemmas -/

/-- For every `m : ℕ` and `t ≥ 0`, `t^m * exp(-3 t^2) ≤ exp(1) * (1 + m!) * exp(-t)`. -/
lemma pow_mul_exp_neg_three_sq_le (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ m * Real.exp (-3 * t ^ 2) ≤ Real.exp 1 * (1 + (m.factorial : ℝ)) * Real.exp (-t) := by
  have hexp_split : Real.exp (-3 * t ^ 2) = Real.exp (-2 * t ^ 2) * Real.exp (-t ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsq : Real.exp (-t ^ 2) ≤ Real.exp 1 * Real.exp (-t) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (t - 1 / 2)]
  have htm : t ^ m ≤ 1 + t ^ (2 * m) := by
    by_cases h1 : t ≤ 1
    · have : t ^ m ≤ 1 := pow_le_one₀ ht h1
      have : 0 ≤ t ^ (2 * m) := pow_nonneg ht _
      linarith
    · push Not at h1
      have hle : t ^ m ≤ t ^ (2 * m) := pow_le_pow_right₀ (le_of_lt h1) (by omega)
      linarith
  have hpow2 : t ^ (2 * m) ≤ (m.factorial : ℝ) * Real.exp (2 * t ^ 2) := by
    have hfac := Real.pow_div_factorial_le_exp (2 * t ^ 2) (by positivity) m
    have h1 : t ^ (2 * m) = (t ^ 2) ^ m := by rw [← pow_mul]
    have h2 : (t ^ 2) ^ m ≤ (2 * t ^ 2) ^ m :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) m
    have h3 : (2 * t ^ 2) ^ m ≤ (m.factorial : ℝ) * Real.exp (2 * t ^ 2) := by
      have hfpos : (0 : ℝ) < (m.factorial : ℝ) := by positivity
      have h' := (div_le_iff₀ hfpos).mp hfac
      linarith
    linarith
  have hbound1 : t ^ m * Real.exp (-2 * t ^ 2) ≤ 1 + (m.factorial : ℝ) := by
    have hpos : 0 < Real.exp (-2 * t ^ 2) := Real.exp_pos _
    have hinv : Real.exp (2 * t ^ 2) * Real.exp (-2 * t ^ 2) = 1 := by
      rw [← Real.exp_add]; simp
    have hle1 : Real.exp (-2 * t ^ 2) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith)
    calc t ^ m * Real.exp (-2 * t ^ 2)
        ≤ (1 + t ^ (2 * m)) * Real.exp (-2 * t ^ 2) := mul_le_mul_of_nonneg_right htm (le_of_lt hpos)
      _ = Real.exp (-2 * t ^ 2) + t ^ (2 * m) * Real.exp (-2 * t ^ 2) := by ring
      _ ≤ 1 + ((m.factorial : ℝ) * Real.exp (2 * t ^ 2)) * Real.exp (-2 * t ^ 2) := by
          gcongr
      _ = 1 + (m.factorial : ℝ) := by rw [mul_assoc, hinv, mul_one]
  calc t ^ m * Real.exp (-3 * t ^ 2)
      = (t ^ m * Real.exp (-2 * t ^ 2)) * Real.exp (-t ^ 2) := by rw [hexp_split]; ring
    _ ≤ (1 + (m.factorial : ℝ)) * (Real.exp 1 * Real.exp (-t)) := by
        exact mul_le_mul hbound1 hsq (le_of_lt (Real.exp_pos _)) (by positivity)
    _ = Real.exp 1 * (1 + (m.factorial : ℝ)) * Real.exp (-t) := by ring

/-- Geometric sum upper bound: for `0 < h ≤ 1`, `∑_{k=1}^K exp(-k h) ≤ 3 / h`. -/
lemma sum_exp_neg_step_le {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, Real.exp (-(k : ℝ) * h) ≤ 3 / h := by
  have hr_lt1 : Real.exp (-h) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hsum_le : ∑ k ∈ Finset.Icc 1 K, Real.exp (-(k : ℝ) * h) ≤
      ∑ k ∈ Finset.range (K + 1), (Real.exp (-h)) ^ k := by
    have hrew : ∑ k ∈ Finset.Icc 1 K, Real.exp (-(k : ℝ) * h) =
        ∑ k ∈ Finset.Icc 1 K, (Real.exp (-h)) ^ k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hrew]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro k hk; rw [mem_Icc] at hk; rw [mem_range]; omega
  have hgeom : ∑ k ∈ Finset.range (K + 1), (Real.exp (-h)) ^ k ≤ (1 - Real.exp (-h))⁻¹ := by
    rw [geom_sum_eq (ne_of_lt hr_lt1)]
    have hden : 0 < 1 - Real.exp (-h) := by linarith
    have hnum : 1 - Real.exp (-h) ^ (K + 1) ≤ 1 := by
      have : 0 ≤ Real.exp (-h) ^ (K + 1) := by positivity
      linarith
    rw [show (Real.exp (-h) ^ (K + 1) - 1) / (Real.exp (-h) - 1) =
        (1 - Real.exp (-h) ^ (K + 1)) / (1 - Real.exp (-h)) by
      have : Real.exp (-h) - 1 ≠ 0 := by linarith
      have : 1 - Real.exp (-h) ≠ 0 := by linarith
      field_simp; ring]
    rw [div_eq_mul_inv]
    simpa using mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (le_of_lt hden))
  have hinv_le : (1 - Real.exp (-h))⁻¹ ≤ 3 / h := by
    have h1 : Real.exp h ≥ 1 + h := by linarith [Real.add_one_le_exp h]
    have h2 : Real.exp h ≤ 3 := by
      have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      exact le_trans (Real.exp_le_exp.mpr hh1) he1
    have hden : 1 - Real.exp (-h) ≥ h / 3 := by
      have hprod : Real.exp (-h) * Real.exp h = 1 := by rw [← Real.exp_add]; simp
      have hpos_eh : 0 < Real.exp h := Real.exp_pos h
      have hstep : (1 - Real.exp (-h)) * Real.exp h = Real.exp h - 1 := by
        rw [sub_mul, one_mul, hprod]
      have hge : h ≤ (1 - Real.exp (-h)) * Real.exp h := by linarith
      have h3ge : (1 - Real.exp (-h)) * Real.exp h ≤ (1 - Real.exp (-h)) * 3 :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      linarith
    have hden_pos : 0 < 1 - Real.exp (-h) := by linarith
    rw [inv_eq_one_div, div_le_div_iff₀ hden_pos hh0]
    linarith
  exact le_trans hsum_le (le_trans hgeom hinv_le)

/-! ### Part 2: Exact elementary antiderivative and integral of `t^(2j+1) * exp(-3 t^2)` -/

/-- Exact antiderivative of `t^(2j+1) * exp(-3 t^2)`. -/
noncomputable def oddGaussAntideriv (j : ℕ) (t : ℝ) : ℝ :=
  -((j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1))) * Real.exp (-3 * t ^ 2) *
    ∑ i ∈ Finset.range (j + 1), (3 * t ^ 2) ^ i / (i.factorial : ℝ)

lemma hasDerivAt_oddGaussAntideriv (j : ℕ) (t : ℝ) :
    HasDerivAt (oddGaussAntideriv j) (t ^ (2 * j + 1) * Real.exp (-3 * t ^ 2)) t := by
  let S : ℝ → ℝ := fun u => ∑ i ∈ Finset.range (j + 1), (3 * u ^ 2) ^ i / (i.factorial : ℝ)
  have hS : HasDerivAt S
      (6 * t * (S t - (3 * t ^ 2) ^ j / (j.factorial : ℝ))) t := by
    have hterm : ∀ i ∈ Finset.range (j + 1),
        HasDerivAt (fun u => (3 * u ^ 2) ^ i / (i.factorial : ℝ))
          (if i = 0 then 0 else 6 * t * ((3 * t ^ 2) ^ (i - 1) / ((i - 1).factorial : ℝ))) t := by
      intro i _
      cases i with
      | zero =>
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ↓reduceIte]
        exact hasDerivAt_const t (1 : ℝ)
      | succ m =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        have hbase : HasDerivAt (fun u => 3 * u ^ 2) (6 * t) t := by
          have h := (hasDerivAt_pow 2 t).const_mul (3 : ℝ)
          convert h using 1; ring
        have hpow := (hbase.pow (m + 1)).div_const (((m + 1).factorial : ℝ))
        convert hpow using 1
        rw [Nat.factorial_succ]
        have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hmf : (m.factorial : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp
    have hsum := HasDerivAt.sum hterm
    have heqS : (∑ i ∈ Finset.range (j + 1), fun u : ℝ => (3 * u ^ 2) ^ i / (i.factorial : ℝ)) = S := by
      ext u; simp [S]
    rw [heqS] at hsum
    convert hsum using 1
    rw [Finset.sum_range_succ']
    have h0 : (if (0 : ℕ) = 0 then (0 : ℝ) else
        6 * t * ((3 * t ^ 2) ^ (0 - 1) / ((0 - 1).factorial : ℝ))) = 0 := rfl
    rw [h0, add_zero]
    have hsucc : ∑ x ∈ Finset.range j,
        (if x + 1 = 0 then (0 : ℝ) else
          6 * t * ((3 * t ^ 2) ^ (x + 1 - 1) / ((x + 1 - 1).factorial : ℝ))) =
        ∑ x ∈ Finset.range j, 6 * t * ((3 * t ^ 2) ^ x / (x.factorial : ℝ)) := by
      refine Finset.sum_congr rfl fun x _ => by simp
    rw [hsucc, ← Finset.mul_sum]
    dsimp only [S]
    rw [Finset.sum_range_succ]
    ring
  have hexp : HasDerivAt (fun u => Real.exp (-3 * u ^ 2)) (-6 * t * Real.exp (-3 * t ^ 2)) t := by
    have hbase : HasDerivAt (fun u => -3 * u ^ 2) (-6 * t) t := by
      have h := (hasDerivAt_pow 2 t).const_mul (-3 : ℝ)
      convert h using 1; ring
    have he := hbase.exp
    convert he using 1; ring
  have hprod := (hexp.mul hS).const_mul (-((j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1))))
  have heq_fn : (fun u => -((j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1))) *
      ((fun u => Real.exp (-3 * u ^ 2)) * S) u) = oddGaussAntideriv j := by
    ext u; unfold oddGaussAntideriv; simp only [Pi.mul_apply, S]; ring
  rw [heq_fn] at hprod
  convert hprod using 1
  have hfj : (j.factorial : ℝ) ≠ 0 := by positivity
  have h3j : (3 : ℝ) ^ (j + 1) ≠ 0 := by positivity
  rw [mul_pow, ← pow_mul, pow_succ (3 : ℝ), pow_succ t]
  field_simp
  ring

/-- Exact finite integral of `t^(2j+1) * exp(-3 t^2)` on `[0, M]`. -/
lemma integral_oddGauss (j : ℕ) (M : ℝ) :
    ∫ t in (0 : ℝ)..M, t ^ (2 * j + 1) * Real.exp (-3 * t ^ 2) =
      (j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1)) *
        (1 - Real.exp (-3 * M ^ 2) * ∑ i ∈ Finset.range (j + 1), (3 * M ^ 2) ^ i / (i.factorial : ℝ)) := by
  have hcont : Continuous (fun t : ℝ => t ^ (2 * j + 1) * Real.exp (-3 * t ^ 2)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_oddGaussAntideriv j t)
      (hcont.intervalIntegrable 0 M)]
  unfold oddGaussAntideriv
  have h0 : ∑ i ∈ Finset.range (j + 1), ((3 : ℝ) * 0 ^ 2) ^ i / (i.factorial : ℝ) = 1 := by
    rw [Finset.sum_range_succ']
    simp
  rw [h0]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Real.exp_zero, mul_one]
  ring

/-! ### Part 3: Cubic Euler-Maclaurin on `[0, K h]` via a single Fundamental Theorem of Calculus -/

/-- First Bernoulli-like polynomial `P1` scaled to `[0, h]`. -/
noncomputable def emP1 (h u : ℝ) : ℝ := u - h / 2
/-- Second Bernoulli-like polynomial `P2` scaled to `[0, h]`. -/
noncomputable def emP2 (h u : ℝ) : ℝ := u ^ 2 / 2 - h * u / 2 + h ^ 2 / 12
/-- Third Bernoulli-like polynomial `P3` scaled to `[0, h]`. -/
noncomputable def emP3 (h u : ℝ) : ℝ := u ^ 3 / 6 - h * u ^ 2 / 4 + h ^ 2 * u / 12

lemma emP3_abs_le {h u : ℝ} (hu0 : 0 ≤ u) (huh : u ≤ h) : |emP3 h u| ≤ h ^ 3 := by
  unfold emP3
  rw [abs_le]
  have hh : 0 ≤ h := le_trans hu0 huh
  have hu2 : u ^ 2 ≤ h ^ 2 := by nlinarith
  have hu3 : u ^ 3 ≤ h ^ 3 := by nlinarith
  have h1 : 0 ≤ u ^ 3 := by positivity
  have h2 : 0 ≤ h * u ^ 2 := by positivity
  have h3 : 0 ≤ h ^ 2 * u := by positivity
  have h4 : h * u ^ 2 ≤ h ^ 3 := by nlinarith
  have h5 : h ^ 2 * u ≤ h ^ 3 := by nlinarith
  constructor <;> linarith

/-- One-step cubic Euler-Maclaurin identity on `[a, a + h]`. -/
lemma euler_maclaurin_step {g g1 g2 g3 : ℝ → ℝ} {a h : ℝ}
    (hg : ∀ t, HasDerivAt g (g1 t) t)
    (hg1 : ∀ t, HasDerivAt g1 (g2 t) t)
    (hg2 : ∀ t, HasDerivAt g2 (g3 t) t)
    (hg3 : Continuous g3) :
    (∫ t in a..(a + h), g t) + (∫ t in a..(a + h), emP3 h (t - a) * g3 t) =
      (h / 2) * (g a + g (a + h)) - (h ^ 2 / 12) * (g1 (a + h) - g1 a) := by
  let Ψ : ℝ → ℝ := fun t => emP1 h (t - a) * g t - emP2 h (t - a) * g1 t + emP3 h (t - a) * g2 t
  have hΨ : ∀ t, HasDerivAt Ψ (g t + emP3 h (t - a) * g3 t) t := by
    intro t
    have hta : HasDerivAt (fun u => u - a) 1 t := (hasDerivAt_id t).sub_const a
    have hP1 : HasDerivAt (fun u => emP1 h (u - a)) 1 t := by
      unfold emP1; simpa using hta.sub_const (h / 2)
    have hP2 : HasDerivAt (fun u => emP2 h (u - a)) (emP1 h (t - a)) t := by
      unfold emP2 emP1
      have hsq := ((hta.pow 2).div_const 2).sub (hta.const_mul (h / 2))
      have hadd := hsq.add_const (h ^ 2 / 12)
      convert hadd using 1
      · ext u; simp only [Pi.sub_apply, Pi.pow_apply]; ring
      · ring
    have hP3 : HasDerivAt (fun u => emP3 h (u - a)) (emP2 h (t - a)) t := by
      unfold emP3 emP2
      have hcb := ((hta.pow 3).div_const 6).sub ((hta.pow 2).const_mul (h / 4))
      have hadd := hcb.add (hta.const_mul (h ^ 2 / 12))
      convert hadd using 1
      · ext u; simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring
      · ring
    have hd := ((hP1.mul (hg t)).sub (hP2.mul (hg1 t))).add (hP3.mul (hg2 t))
    convert hd using 1; ring
  have hcont_g : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have hcont_rem : Continuous (fun t => emP3 h (t - a) * g3 t) := by
    unfold emP3; fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := a + h)
    (fun t _ => hΨ t) ((hcont_g.add hcont_rem).intervalIntegrable a (a + h))
  rw [intervalIntegral.integral_add (hcont_g.intervalIntegrable a (a + h))
      (hcont_rem.intervalIntegrable a (a + h))] at hint
  rw [hint]
  dsimp only [Ψ, emP1, emP2, emP3]
  simp only [add_sub_cancel_left, sub_self]
  ring

private lemma sum_adjacent_integrals {f : ℝ → ℝ} (hf : Continuous f) (h : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, ∫ t in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), f t =
      ∫ t in (0 : ℝ)..((N : ℝ) * h), f t := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

private lemma sum_trapezoidal_zero {g : ℝ → ℝ} (hg0 : g 0 = 0) (h : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, (h / 2) * (g ((k : ℝ) * h) + g (((k + 1 : ℕ) : ℝ) * h)) =
      h * (∑ k ∈ Finset.Icc 1 N, g ((k : ℝ) * h)) - (h / 2) * g ((N : ℝ) * h) := by
  induction N with
  | zero => simp [hg0]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hIcc : ∑ k ∈ Finset.Icc 1 (n + 1), g ((k : ℝ) * h) =
        (∑ k ∈ Finset.Icc 1 n, g ((k : ℝ) * h)) + g (((n + 1 : ℕ) : ℝ) * h) := by
      have hsub : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [hsub, Finset.sum_insert (by simp)]
      ring
    rw [hIcc]
    ring

/-- Multi-step cubic Euler-Maclaurin bound on `[0, K * h]` for any `C^3` function `g` with `g 0 = 0`. -/
lemma euler_maclaurin_sum_bound {g g1 g2 g3 : ℝ → ℝ} {h : ℝ} (hh : 0 < h) (K : ℕ)
    (hg0 : g 0 = 0)
    (hg : ∀ t, HasDerivAt g (g1 t) t)
    (hg1 : ∀ t, HasDerivAt g1 (g2 t) t)
    (hg2 : ∀ t, HasDerivAt g2 (g3 t) t)
    (hg3 : Continuous g3) :
    |h * (∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) * h)) -
      (∫ t in (0 : ℝ)..((K : ℝ) * h), g t) +
      (h ^ 2 / 12) * g1 0 -
      (h / 2) * g ((K : ℝ) * h) -
      (h ^ 2 / 12) * g1 ((K : ℝ) * h)| ≤
      h ^ 3 * ∫ t in (0 : ℝ)..((K : ℝ) * h), |g3 t| := by
  have hcont_g : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have hsum_step :
      (∑ k ∈ Finset.range K, ∫ t in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), g t) +
      (∑ k ∈ Finset.range K, ∫ t in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), emP3 h (t - (k : ℝ) * h) * g3 t) =
      (∑ k ∈ Finset.range K, (h / 2) * (g ((k : ℝ) * h) + g (((k + 1 : ℕ) : ℝ) * h))) -
      (∑ k ∈ Finset.range K, (h ^ 2 / 12) * (g1 (((k + 1 : ℕ) : ℝ) * h) - g1 ((k : ℝ) * h))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have heq : ((k + 1 : ℕ) : ℝ) * h = (k : ℝ) * h + h := by push_cast; ring
    rw [heq]
    exact euler_maclaurin_step hg hg1 hg2 hg3
  have hint_g := sum_adjacent_integrals hcont_g h K
  have htel_g1 : ∑ k ∈ Finset.range K, (h ^ 2 / 12) * (g1 (((k + 1 : ℕ) : ℝ) * h) - g1 ((k : ℝ) * h)) =
      (h ^ 2 / 12) * (g1 ((K : ℝ) * h) - g1 0) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => g1 ((k : ℝ) * h)) K]
    simp
  have htrap_g := sum_trapezoidal_zero hg0 h K
  rw [hint_g, htel_g1, htrap_g] at hsum_step
  have hrem_eq :
      h * (∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) * h)) -
        (∫ t in (0 : ℝ)..((K : ℝ) * h), g t) +
        (h ^ 2 / 12) * g1 0 -
        (h / 2) * g ((K : ℝ) * h) -
        (h ^ 2 / 12) * g1 ((K : ℝ) * h) =
      ∑ k ∈ Finset.range K, ∫ t in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h),
        emP3 h (t - (k : ℝ) * h) * g3 t := by
    linarith
  rw [hrem_eq]
  have hint_abs := sum_adjacent_integrals hg3.abs h K
  rw [← hint_abs, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun k _ => ?_
  have hle : (k : ℝ) * h ≤ ((k + 1 : ℕ) : ℝ) * h := by
    have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact mul_le_mul_of_nonneg_right this (le_of_lt hh)
  have hcont_p3 : Continuous (fun t => emP3 h (t - (k : ℝ) * h) * g3 t) := by
    unfold emP3; fun_prop
  calc |∫ t in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), emP3 h (t - (k : ℝ) * h) * g3 t|
      ≤ ∫ t in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), |emP3 h (t - (k : ℝ) * h) * g3 t| :=
        intervalIntegral.abs_integral_le_integral_abs hle
    _ ≤ ∫ t in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), h ^ 3 * |g3 t| := by
        refine intervalIntegral.integral_mono_on hle (hcont_p3.abs.intervalIntegrable _ _)
          ((hg3.abs.const_mul (h ^ 3)).intervalIntegrable _ _) fun t ht => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have ht1 : 0 ≤ t - (k : ℝ) * h := by linarith [ht.1]
        have ht2 : t - (k : ℝ) * h ≤ h := by
          have : ((k + 1 : ℕ) : ℝ) * h = (k : ℝ) * h + h := by push_cast; ring
          linarith [ht.2]
        exact emP3_abs_le ht1 ht2
    _ = h ^ 3 * ∫ t in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), |g3 t| :=
        intervalIntegral.integral_const_mul _ _

/-! ### Part 4: Specialized Euler-Maclaurin approximation for `g_j(t) = t^(2j+1) * exp(-3 t^2)` -/

/-- Derivative of `t^m * exp(-3 t^2)`. -/
lemma hasDerivAt_poly_exp (m : ℕ) (t : ℝ) :
    HasDerivAt (fun u => u ^ m * Real.exp (-3 * u ^ 2))
      (((m : ℝ) * t ^ (m - 1) - 6 * t ^ (m + 1)) * Real.exp (-3 * t ^ 2)) t := by
  have hexp : HasDerivAt (fun u => Real.exp (-3 * u ^ 2)) (-6 * t * Real.exp (-3 * t ^ 2)) t := by
    have hbase : HasDerivAt (fun u => -3 * u ^ 2) (-6 * t) t := by
      have h := (hasDerivAt_pow 2 t).const_mul (-3 : ℝ)
      convert h using 1; ring
    have he := hbase.exp
    convert he using 1; ring
  have hprod := (hasDerivAt_pow m t).mul hexp
  convert hprod using 1
  cases m with
  | zero => simp
  | succ k => simp [pow_succ]; ring

/-- Clean uniform Euler-Maclaurin bound for `t^(2j+1) * exp(-3 t^2)` on `k = 1..K`. -/
theorem oddGauss_sum_approx (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → ∀ K : ℕ,
      |h * (∑ k ∈ Finset.Icc 1 K, ((k : ℝ) * h) ^ (2 * j + 1) * Real.exp (-3 * ((k : ℝ) * h) ^ 2)) -
        ((j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1)) - if j = 0 then h ^ 2 / 12 else 0)| ≤
        C * (h ^ 3 + (1 + h + h ^ 2) * Real.exp (-((K : ℝ) * h))) := by
  set m := 2 * j + 1
  let g : ℝ → ℝ := fun t => t ^ m * Real.exp (-3 * t ^ 2)
  let g1 : ℝ → ℝ := fun t => ((m : ℝ) * t ^ (m - 1) - 6 * t ^ (m + 1)) * Real.exp (-3 * t ^ 2)
  let g2 : ℝ → ℝ := fun t =>
    ((m : ℝ) * (((m - 1 : ℕ) : ℝ) * t ^ (m - 2) - 6 * t ^ m) -
     6 * (((m + 1 : ℕ) : ℝ) * t ^ m - 6 * t ^ (m + 2))) * Real.exp (-3 * t ^ 2)
  let g3 : ℝ → ℝ := fun t =>
    ((m : ℝ) * (((m - 1 : ℕ) : ℝ) * (((m - 2 : ℕ) : ℝ) * t ^ (m - 3) - 6 * t ^ (m - 1)) -
                6 * ((m : ℝ) * t ^ (m - 1) - 6 * t ^ (m + 1))) -
     6 * (((m + 1 : ℕ) : ℝ) * ((m : ℝ) * t ^ (m - 1) - 6 * t ^ (m + 1)) -
          6 * (((m + 2 : ℕ) : ℝ) * t ^ (m + 1) - 6 * t ^ (m + 3)))) * Real.exp (-3 * t ^ 2)
  have hg : ∀ t, HasDerivAt g (g1 t) t := fun t => hasDerivAt_poly_exp m t
  have hg1 : ∀ t, HasDerivAt g1 (g2 t) t := by
    intro t
    have hrew : g1 = fun u => (m : ℝ) * (u ^ (m - 1) * Real.exp (-3 * u ^ 2)) -
        6 * (u ^ (m + 1) * Real.exp (-3 * u ^ 2)) := by ext u; dsimp only [g1]; ring
    rw [hrew]
    have hd := ((hasDerivAt_poly_exp (m - 1) t).const_mul (m : ℝ)).sub
      ((hasDerivAt_poly_exp (m + 1) t).const_mul 6)
    convert hd using 1
    have h1 : m - 1 - 1 = m - 2 := by omega
    have h2 : m - 1 + 1 = m := by omega
    have h3 : m + 1 - 1 = m := by omega
    have h4 : m + 1 + 1 = m + 2 := by omega
    rw [h1, h2, h3, h4]
    dsimp only [g2]; ring
  have hg2 : ∀ t, HasDerivAt g2 (g3 t) t := by
    intro t
    have hrew : g2 = fun u =>
        (m : ℝ) * (((m - 1 : ℕ) : ℝ) * (u ^ (m - 2) * Real.exp (-3 * u ^ 2)) -
                   6 * (u ^ m * Real.exp (-3 * u ^ 2))) -
        6 * (((m + 1 : ℕ) : ℝ) * (u ^ m * Real.exp (-3 * u ^ 2)) -
             6 * (u ^ (m + 2) * Real.exp (-3 * u ^ 2))) := by
      ext u; dsimp only [g2]; ring
    rw [hrew]
    have hd := (((hasDerivAt_poly_exp (m - 2) t).const_mul ((m - 1 : ℕ) : ℝ)).sub
        ((hasDerivAt_poly_exp m t).const_mul 6) |>.const_mul (m : ℝ)).sub
      (((hasDerivAt_poly_exp m t).const_mul ((m + 1 : ℕ) : ℝ)).sub
        ((hasDerivAt_poly_exp (m + 2) t).const_mul 6) |>.const_mul 6)
    convert hd using 1
    have h1 : m - 2 - 1 = m - 3 := by omega
    have h3 : m + 2 - 1 = m + 1 := by omega
    have h4 : m + 2 + 1 = m + 3 := by omega
    rw [h1, h3, h4]
    dsimp only [g3]
    cases j with
    | zero =>
      have hm1 : m = 1 := rfl
      simp only [hm1, Nat.sub_self, Nat.cast_zero, zero_mul, zero_sub]
      ring
    | succ j' =>
      have h2 : m - 2 + 1 = m - 1 := by dsimp only [m]; omega
      rw [h2]
      ring
  have hg3_cont : Continuous g3 := by dsimp only [g3]; fun_prop
  have hg0 : g 0 = 0 := by
    dsimp only [g]
    rw [zero_pow (by omega : m ≠ 0), zero_mul]
  have hg1_0 : g1 0 = if j = 0 then 1 else 0 := by
    dsimp only [g1]
    cases j with
    | zero => simp [m]
    | succ j' =>
      have hm1 : m - 1 ≠ 0 := by dsimp only [m]; omega
      have hm2 : m + 1 ≠ 0 := by dsimp only [m]; omega
      simp [zero_pow hm1, zero_pow hm2]
  let E : ℕ → ℝ := fun k => Real.exp 1 * (1 + (k.factorial : ℝ))
  have hE_nn : ∀ k, 0 ≤ E k := fun k => by dsimp only [E]; positivity
  have hg_dom : ∀ {t : ℝ}, 0 ≤ t → |g t| ≤ E m * Real.exp (-t) := by
    intro t ht
    dsimp only [g, E]
    rw [abs_of_nonneg (by positivity)]
    exact pow_mul_exp_neg_three_sq_le m ht
  have hg1_dom : ∀ {t : ℝ}, 0 ≤ t → |g1 t| ≤ ((m : ℝ) * E (m - 1) + 6 * E (m + 1)) * Real.exp (-t) := by
    intro t ht
    dsimp only [g1]
    rw [sub_mul]
    refine le_trans (abs_sub _ _) ?_
    have h1 : |(m : ℝ) * t ^ (m - 1) * Real.exp (-3 * t ^ 2)| ≤ (m : ℝ) * (E (m - 1) * Real.exp (-t)) := by
      rw [mul_assoc, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (pow_mul_exp_neg_three_sq_le (m - 1) ht) (by positivity)
    have h2 : |6 * t ^ (m + 1) * Real.exp (-3 * t ^ 2)| ≤ 6 * (E (m + 1) * Real.exp (-t)) := by
      rw [mul_assoc, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (pow_mul_exp_neg_three_sq_le (m + 1) ht) (by positivity)
    linarith
  set B3 : ℝ :=
    (m : ℝ) * (((m - 1 : ℕ) : ℝ) * (((m - 2 : ℕ) : ℝ) * E (m - 3) + 6 * E (m - 1)) +
               6 * ((m : ℝ) * E (m - 1) + 6 * E (m + 1))) +
    6 * (((m + 1 : ℕ) : ℝ) * ((m : ℝ) * E (m - 1) + 6 * E (m + 1)) +
         6 * (((m + 2 : ℕ) : ℝ) * E (m + 1) + 6 * E (m + 3)))
  have hB3_nn : 0 ≤ B3 := by dsimp only [B3, E]; positivity
  have hg3_dom : ∀ {t : ℝ}, 0 ≤ t → |g3 t| ≤ B3 * Real.exp (-t) := by
    intro t ht
    have hterm : ∀ (c : ℝ) (k : ℕ), 0 ≤ c →
        |c * (t ^ k * Real.exp (-3 * t ^ 2))| ≤ c * E k * Real.exp (-t) := by
      intro c k hc
      rw [abs_mul, abs_of_nonneg hc, abs_of_nonneg (by positivity), mul_assoc]
      exact mul_le_mul_of_nonneg_left (pow_mul_exp_neg_three_sq_le k ht) hc
    have hrew : g3 t =
        ((m : ℝ) * ((m - 1 : ℕ) : ℝ) * ((m - 2 : ℕ) : ℝ) * (t ^ (m - 3) * Real.exp (-3 * t ^ 2)) -
         (m : ℝ) * ((m - 1 : ℕ) : ℝ) * 6 * (t ^ (m - 1) * Real.exp (-3 * t ^ 2))) -
        ((m : ℝ) * 6 * (m : ℝ) * (t ^ (m - 1) * Real.exp (-3 * t ^ 2)) -
         (m : ℝ) * 6 * 6 * (t ^ (m + 1) * Real.exp (-3 * t ^ 2))) -
        ((6 * ((m + 1 : ℕ) : ℝ) * (m : ℝ) * (t ^ (m - 1) * Real.exp (-3 * t ^ 2)) -
          6 * ((m + 1 : ℕ) : ℝ) * 6 * (t ^ (m + 1) * Real.exp (-3 * t ^ 2))) -
         (6 * 6 * ((m + 2 : ℕ) : ℝ) * (t ^ (m + 1) * Real.exp (-3 * t ^ 2)) -
          6 * 6 * 6 * (t ^ (m + 3) * Real.exp (-3 * t ^ 2)))) := by
      dsimp only [g3]; ring
    rw [hrew]
    have h1 := hterm ((m : ℝ) * ((m - 1 : ℕ) : ℝ) * ((m - 2 : ℕ) : ℝ)) (m - 3) (by positivity)
    have h2 := hterm ((m : ℝ) * ((m - 1 : ℕ) : ℝ) * 6) (m - 1) (by positivity)
    have h3 := hterm ((m : ℝ) * 6 * (m : ℝ)) (m - 1) (by positivity)
    have h4 := hterm ((m : ℝ) * 6 * 6) (m + 1) (by positivity)
    have h5 := hterm (6 * ((m + 1 : ℕ) : ℝ) * (m : ℝ)) (m - 1) (by positivity)
    have h6 := hterm (6 * ((m + 1 : ℕ) : ℝ) * 6) (m + 1) (by positivity)
    have h7 := hterm (6 * 6 * ((m + 2 : ℕ) : ℝ)) (m + 1) (by positivity)
    have h8 := hterm (6 * 6 * 6) (m + 3) (by positivity)
    set U1 := (m : ℝ) * ((m - 1 : ℕ) : ℝ) * ((m - 2 : ℕ) : ℝ) * (t ^ (m - 3) * Real.exp (-3 * t ^ 2))
    set U2 := (m : ℝ) * ((m - 1 : ℕ) : ℝ) * 6 * (t ^ (m - 1) * Real.exp (-3 * t ^ 2))
    set U3 := (m : ℝ) * 6 * (m : ℝ) * (t ^ (m - 1) * Real.exp (-3 * t ^ 2))
    set U4 := (m : ℝ) * 6 * 6 * (t ^ (m + 1) * Real.exp (-3 * t ^ 2))
    set U5 := 6 * ((m + 1 : ℕ) : ℝ) * (m : ℝ) * (t ^ (m - 1) * Real.exp (-3 * t ^ 2))
    set U6 := 6 * ((m + 1 : ℕ) : ℝ) * 6 * (t ^ (m + 1) * Real.exp (-3 * t ^ 2))
    set U7 := 6 * 6 * ((m + 2 : ℕ) : ℝ) * (t ^ (m + 1) * Real.exp (-3 * t ^ 2))
    set U8 := 6 * 6 * 6 * (t ^ (m + 3) * Real.exp (-3 * t ^ 2))
    have htri : |((U1 - U2) - (U3 - U4)) - ((U5 - U6) - (U7 - U8))| ≤
        |U1| + |U2| + |U3| + |U4| + |U5| + |U6| + |U7| + |U8| := by
      linarith [abs_sub ((U1 - U2) - (U3 - U4)) ((U5 - U6) - (U7 - U8)),
        abs_sub (U1 - U2) (U3 - U4), abs_sub (U5 - U6) (U7 - U8),
        abs_sub U1 U2, abs_sub U3 U4, abs_sub U5 U6, abs_sub U7 U8]
    dsimp only [B3]
    linarith
  set Bint : ℝ := ((j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1))) *
      ∑ i ∈ Finset.range (j + 1), (3 : ℝ) ^ i * E (2 * i) / (i.factorial : ℝ)
  have hBint_nn : 0 ≤ Bint := by dsimp only [Bint, E]; positivity
  have hint_tail : ∀ {M : ℝ}, 0 ≤ M →
      |(∫ t in (0 : ℝ)..M, g t) - (j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1))| ≤
        Bint * Real.exp (-M) := by
    intro M hM
    dsimp only [g, m]
    rw [integral_oddGauss j M]
    set c := (j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1))
    have hc : 0 ≤ c := by positivity
    have hdiff : c * (1 - Real.exp (-3 * M ^ 2) * ∑ i ∈ Finset.range (j + 1), (3 * M ^ 2) ^ i / (i.factorial : ℝ)) - c =
        -(c * ∑ i ∈ Finset.range (j + 1), ((3 : ℝ) ^ i / (i.factorial : ℝ)) * (M ^ (2 * i) * Real.exp (-3 * M ^ 2))) := by
      have hsum_eq : Real.exp (-3 * M ^ 2) * ∑ i ∈ Finset.range (j + 1), (3 * M ^ 2) ^ i / (i.factorial : ℝ) =
          ∑ i ∈ Finset.range (j + 1), ((3 : ℝ) ^ i / (i.factorial : ℝ)) * (M ^ (2 * i) * Real.exp (-3 * M ^ 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, ← pow_mul]; ring
      rw [hsum_eq]; ring
    rw [hdiff, abs_neg, abs_of_nonneg (by positivity)]
    dsimp only [Bint]
    rw [mul_assoc, Finset.sum_mul]
    refine mul_le_mul_of_nonneg_left ?_ hc
    refine Finset.sum_le_sum fun i _ => ?_
    have hle := pow_mul_exp_neg_three_sq_le (2 * i) hM
    have hfac : 0 ≤ (3 : ℝ) ^ i / (i.factorial : ℝ) := by positivity
    calc ((3 : ℝ) ^ i / (i.factorial : ℝ)) * (M ^ (2 * i) * Real.exp (-3 * M ^ 2))
        ≤ ((3 : ℝ) ^ i / (i.factorial : ℝ)) * (E (2 * i) * Real.exp (-M)) :=
          mul_le_mul_of_nonneg_left hle hfac
      _ = (3 : ℝ) ^ i * E (2 * i) / (i.factorial : ℝ) * Real.exp (-M) := by ring
  set B1 : ℝ := (m : ℝ) * E (m - 1) + 6 * E (m + 1)
  have hB1_nn : 0 ≤ B1 := by dsimp only [B1, E]; positivity
  refine ⟨B3 + Bint + E m + B1, by positivity, ?_⟩
  intro h hh K
  set M : ℝ := (K : ℝ) * h
  have hM : 0 ≤ M := by positivity
  have hem := euler_maclaurin_sum_bound hh K hg0 hg hg1 hg2 hg3_cont
  have hint_g3 : ∫ t in (0 : ℝ)..M, |g3 t| ≤ B3 := by
    have hle1 : ∫ t in (0 : ℝ)..M, |g3 t| ≤ ∫ t in (0 : ℝ)..M, B3 * Real.exp (-t) := by
      refine intervalIntegral.integral_mono_on hM (hg3_cont.abs.intervalIntegrable 0 M)
        ((by fun_prop : Continuous fun t => B3 * Real.exp (-t)).intervalIntegrable 0 M) fun t ht =>
          hg3_dom ht.1
    have hderiv_exp : ∀ t, HasDerivAt (fun u => -B3 * Real.exp (-u)) (B3 * Real.exp (-t)) t := by
      intro t
      have h1 : HasDerivAt (fun u => -u) (-1) t := (hasDerivAt_id t).neg
      have h2 := h1.exp.const_mul (-B3)
      convert h2 using 1; ring
    have heval : ∫ t in (0 : ℝ)..M, B3 * Real.exp (-t) = B3 * (1 - Real.exp (-M)) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv_exp t)
          ((by fun_prop : Continuous fun t => B3 * Real.exp (-t)).intervalIntegrable 0 M)]
      simp; ring
    rw [heval] at hle1
    have hexp_pos : 0 ≤ Real.exp (-M) := le_of_lt (Real.exp_pos _)
    nlinarith
  have hem_val : |h * (∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) * h)) - (∫ t in (0 : ℝ)..M, g t) +
      (if j = 0 then h ^ 2 / 12 else 0) - (h / 2) * g M - (h ^ 2 / 12) * g1 M| ≤ h ^ 3 * B3 := by
    have hrew : (h ^ 2 / 12) * g1 0 = if j = 0 then h ^ 2 / 12 else 0 := by
      rw [hg1_0]; split_ifs <;> ring
    rw [hrew] at hem
    exact le_trans hem (mul_le_mul_of_nonneg_left hint_g3 (by positivity))
  set A1 := h * (∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) * h)) - (∫ t in (0 : ℝ)..M, g t) +
      (if j = 0 then h ^ 2 / 12 else 0) - (h / 2) * g M - (h ^ 2 / 12) * g1 M
  set A2 := (∫ t in (0 : ℝ)..M, g t) - (j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1))
  set A3 := (h / 2) * g M
  set A4 := (h ^ 2 / 12) * g1 M
  have hdecomp :
      h * (∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) * h)) -
        ((j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1)) - if j = 0 then h ^ 2 / 12 else 0) =
      A1 + A2 + A3 + A4 := by
    dsimp only [A1, A2, A3, A4]; ring
  change |h * (∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) * h)) -
    ((j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1)) - if j = 0 then h ^ 2 / 12 else 0)| ≤ _
  rw [hdecomp]
  have h1 : |A1| ≤ h ^ 3 * B3 := hem_val
  have h2 : |A2| ≤ Bint * Real.exp (-M) := hint_tail hM
  have h3 : |A3| ≤ h * E m * Real.exp (-M) := by
    dsimp only [A3]
    rw [abs_mul, abs_of_pos (by positivity)]
    have hgM := hg_dom hM
    have hmul := mul_le_mul_of_nonneg_left hgM (by positivity : 0 ≤ h / 2)
    have hstep : h / 2 * (E m * Real.exp (-M)) ≤ h * E m * Real.exp (-M) := by
      have : 0 ≤ h * E m * Real.exp (-M) := by positivity
      linarith [show h / 2 * (E m * Real.exp (-M)) = (1 / 2 : ℝ) * (h * E m * Real.exp (-M)) by ring]
    exact le_trans hmul hstep
  have h4 : |A4| ≤ h ^ 2 * B1 * Real.exp (-M) := by
    dsimp only [A4]
    rw [abs_mul, abs_of_pos (by positivity)]
    have hg1M := hg1_dom hM
    have hmul := mul_le_mul_of_nonneg_left hg1M (by positivity : 0 ≤ h ^ 2 / 12)
    have hstep : h ^ 2 / 12 * (B1 * Real.exp (-M)) ≤ h ^ 2 * B1 * Real.exp (-M) := by
      have : 0 ≤ h ^ 2 * B1 * Real.exp (-M) := by positivity
      linarith [show h ^ 2 / 12 * (B1 * Real.exp (-M)) = (1 / 12 : ℝ) * (h ^ 2 * B1 * Real.exp (-M)) by ring]
    exact le_trans hmul hstep
  have htri : |A1 + A2 + A3 + A4| ≤ |A1| + |A2| + |A3| + |A4| := by
    linarith [abs_add_le (A1 + A2 + A3) A4, abs_add_le (A1 + A2) A3, abs_add_le A1 A2]
  have hexp_nn : 0 ≤ Real.exp (-M) := le_of_lt (Real.exp_pos _)
  have hh3_nn : 0 ≤ h ^ 3 := by positivity
  have hh2_nn : 0 ≤ h ^ 2 := by positivity
  have hterm1 : h ^ 3 * B3 ≤ (B3 + Bint + E m + B1) * h ^ 3 := by
    have : 0 ≤ (Bint + E m + B1) * h ^ 3 := by positivity
    linarith
  have hterm2 : Bint * Real.exp (-M) + h * E m * Real.exp (-M) + h ^ 2 * B1 * Real.exp (-M) ≤
      (B3 + Bint + E m + B1) * ((1 + h + h ^ 2) * Real.exp (-M)) := by
    have hdiff_nn : 0 ≤ (B3 * (1 + h + h ^ 2) + Bint * (h + h ^ 2) +
        E m * (1 + h ^ 2) + B1 * (1 + h)) * Real.exp (-M) := by positivity
    linarith
  linarith

end MultinomialTV

end
