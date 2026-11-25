import MultinomialTVConjecture.Combinatorial
import MultinomialTVConjecture.StirlingRefined
import MultinomialTVConjecture.GaussianEulerMaclaurin
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

open scoped BigOperators
open Real Filter Topology Finset

namespace MultinomialTV

/-! ### Part 1: Elementary consecutive-ratio Gaussian tail bounds for `p_{3q}(q ± k)` -/

/-- For `q ≥ 1` and `0 ≤ k ≤ q`, the right ratio satisfies `p3q q (q + k) / p3q q q ≤ exp(-k^2 / (3q))`. -/
lemma p3q_right_ratio_le (q k : ℕ) (hq : 1 ≤ q) :
    p3q q (q + k) / p3q q q ≤ Real.exp (-((k : ℝ) ^ 2) / (3 * (q : ℝ))) := by
  have hp0 : 0 < p3q q q := p3q_center_pos q
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  by_cases h2k : 2 * k ≤ q
  · induction k with
    | zero =>
      simp [div_self (ne_of_gt hp0)]
    | succ j ih =>
      have h2j : 2 * j ≤ q := by omega
      have hih := ih h2j
      have hstep : p3q q (q + (j + 1)) / p3q q q =
          (((q - 2 * j : ℕ) : ℝ) * ((q - 2 * j - 1 : ℕ) : ℝ) / ((q + j + 1 : ℕ) : ℝ) ^ 2) *
            (p3q q (q + j) / p3q q q) := by
        rw [p3q_eq_of_le (x := q + (j + 1)) (by omega), p3q_eq_of_le (x := q + j) (by omega)]
        have h1 : 3 * q - 2 * (q + (j + 1)) = q - 2 * j - 2 := by omega
        have h2 : 3 * q - 2 * (q + j) = q - 2 * j := by omega
        rw [h1, h2]
        have hT1 : (((q + j + 1 : ℕ) : ℝ) ^ 2) * T (q + j + 1) (q + j + 1) (q - 2 * j - 2) =
            T (q + j) (q + j) (q - 2 * j - 2) := by
          have ha := mul_T_fst (q + j) (q + j + 1) (q - 2 * j - 2)
          have hb := mul_T_snd (q + j) (q + j) (q - 2 * j - 2)
          calc (((q + j + 1 : ℕ) : ℝ) ^ 2) * T (q + j + 1) (q + j + 1) (q - 2 * j - 2)
              = ((q + j + 1 : ℕ) : ℝ) * (((q + j + 1 : ℕ) : ℝ) * T (q + j + 1) (q + j + 1) (q - 2 * j - 2)) := by ring
            _ = ((q + j + 1 : ℕ) : ℝ) * T (q + j) (q + j + 1) (q - 2 * j - 2) := by rw [ha]
            _ = T (q + j) (q + j) (q - 2 * j - 2) := hb
        have hT2 : (((q - 2 * j : ℕ) : ℝ) * ((q - 2 * j - 1 : ℕ) : ℝ)) * T (q + j) (q + j) (q - 2 * j) =
            T (q + j) (q + j) (q - 2 * j - 2) := by
          obtain ⟨c, hc⟩ : ∃ c, q - 2 * j = c + 2 := ⟨q - 2 * j - 2, by omega⟩
          have hc1 : q - 2 * j - 1 = c + 1 := by omega
          have hc2 : q - 2 * j - 2 = c := by omega
          rw [hc2, hc1, hc]
          calc (((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ)) * T (q + j) (q + j) (c + 2)
              = ((c + 1 : ℕ) : ℝ) * (((c + 1 + 1 : ℕ) : ℝ) * T (q + j) (q + j) (c + 1 + 1)) := by ring
            _ = ((c + 1 : ℕ) : ℝ) * T (q + j) (q + j) (c + 1) := by rw [mul_T_thd (q + j) (q + j) (c + 1)]
            _ = T (q + j) (q + j) c := mul_T_thd (q + j) (q + j) c
        have hden : ((q + j + 1 : ℕ) : ℝ) ^ 2 ≠ 0 := by positivity
        have hpne : p3q q q ≠ 0 := ne_of_gt hp0
        have hassoc : q + (j + 1) = q + j + 1 := by omega
        rw [hassoc]
        have hT_eq : T (q + j + 1) (q + j + 1) (q - 2 * j - 2) =
            (((q - 2 * j : ℕ) : ℝ) * ((q - 2 * j - 1 : ℕ) : ℝ) / ((q + j + 1 : ℕ) : ℝ) ^ 2) *
              T (q + j) (q + j) (q - 2 * j) := by
          rw [div_mul_eq_mul_div, eq_div_iff hden]
          linarith
        rw [hT_eq]; ring
      have hrat_le : (((q - 2 * j : ℕ) : ℝ) * ((q - 2 * j - 1 : ℕ) : ℝ) / ((q + j + 1 : ℕ) : ℝ) ^ 2) ≤
          Real.exp (-((2 * (j : ℝ) + 1) / (3 * (q : ℝ)))) := by
        have h1 : (((q - 2 * j : ℕ) : ℝ) * ((q - 2 * j - 1 : ℕ) : ℝ) / ((q + j + 1 : ℕ) : ℝ) ^ 2) ≤
            1 - (2 * (j : ℝ) + 1) / (3 * (q : ℝ)) := by
          have hc1 : ((q - 2 * j : ℕ) : ℝ) = (q : ℝ) - 2 * (j : ℝ) := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          have hc2 : ((q - 2 * j - 1 : ℕ) : ℝ) = (q : ℝ) - 2 * (j : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
          have hc3 : ((q + j + 1 : ℕ) : ℝ) = (q : ℝ) + (j : ℝ) + 1 := by push_cast; ring
          rw [hc1, hc2, hc3]
          have hden_pos : 0 < ((q : ℝ) + (j : ℝ) + 1) ^ 2 := by positivity
          have hj_le : 2 * (j : ℝ) + 2 ≤ (q : ℝ) := by exact_mod_cast h2k
          have hj_nn : (0 : ℝ) ≤ (j : ℝ) := by positivity
          rw [div_le_iff₀ hden_pos]
          have hnum : ((q : ℝ) + (j : ℝ) + 1) ^ 2 - ((q : ℝ) - 2 * (j : ℝ)) * ((q : ℝ) - 2 * (j : ℝ) - 1) =
              6 * (q : ℝ) * (j : ℝ) + 3 * (q : ℝ) - 3 * (j : ℝ) ^ 2 + 1 := by ring
          have hq_bound : ((q : ℝ) + (j : ℝ) + 1) ^ 2 ≤ 4 * (q : ℝ) ^ 2 := by nlinarith
          have hdiff_ge : 2 * (q : ℝ) * (2 * (j : ℝ) + 1) ≤
              6 * (q : ℝ) * (j : ℝ) + 3 * (q : ℝ) - 3 * (j : ℝ) ^ 2 + 1 := by nlinarith
          have hkey : (2 * (j : ℝ) + 1) / (3 * (q : ℝ)) * ((q : ℝ) + (j : ℝ) + 1) ^ 2 ≤
              2 * (q : ℝ) * (2 * (j : ℝ) + 1) := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            have h2j1 : 0 ≤ 2 * (j : ℝ) + 1 := by positivity
            nlinarith
          nlinarith
        have h2 := Real.add_one_le_exp (-((2 * (j : ℝ) + 1) / (3 * (q : ℝ))))
        linarith
      have hrat_nn : 0 ≤ p3q q (q + j) / p3q q q := by
        refine div_nonneg ?_ (le_of_lt hp0)
        rw [p3q_eq_of_le (by omega)]
        have := T_pos (q + j) (q + j) (3 * q - 2 * (q + j))
        positivity
      rw [hstep]
      calc (((q - 2 * j : ℕ) : ℝ) * ((q - 2 * j - 1 : ℕ) : ℝ) / ((q + j + 1 : ℕ) : ℝ) ^ 2) *
            (p3q q (q + j) / p3q q q)
          ≤ Real.exp (-((2 * (j : ℝ) + 1) / (3 * (q : ℝ)))) *
              Real.exp (-((j : ℝ) ^ 2) / (3 * (q : ℝ))) :=
            mul_le_mul hrat_le hih hrat_nn (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-(((j + 1 : ℕ) : ℝ) ^ 2) / (3 * (q : ℝ))) := by
            rw [← Real.exp_add]; congr 1; push_cast; ring
  · rw [p3q_eq_zero_of_gt (by omega), zero_div]
    exact le_of_lt (Real.exp_pos _)

/-- For `q ≥ 1` and `0 ≤ k ≤ q`, the left ratio satisfies `p3q q (q - k) / p3q q q ≤ exp(-k^2 / (3q))`. -/
lemma p3q_left_ratio_le (q k : ℕ) (hq : 1 ≤ q) (hk : k ≤ q) :
    p3q q (q - k) / p3q q q ≤ Real.exp (-((k : ℝ) ^ 2) / (3 * (q : ℝ))) := by
  have hp0 : 0 < p3q q q := p3q_center_pos q
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  induction k with
  | zero =>
    simp [div_self (ne_of_gt hp0)]
  | succ j ih =>
    have hih := ih (by omega)
    have hstep : p3q q (q - (j + 1)) / p3q q q =
        (((q - j : ℕ) : ℝ) ^ 2 / (((q + 2 * j + 1 : ℕ) : ℝ) * ((q + 2 * j + 2 : ℕ) : ℝ))) *
          (p3q q (q - j) / p3q q q) := by
      rw [p3q_eq_of_le (x := q - (j + 1)) (by omega), p3q_eq_of_le (x := q - j) (by omega)]
      have h1 : 3 * q - 2 * (q - (j + 1)) = q + 2 * j + 2 := by omega
      have h2 : 3 * q - 2 * (q - j) = q + 2 * j := by omega
      rw [h1, h2]
      have hT1 : (((q - j : ℕ) : ℝ) ^ 2) * T (q - j) (q - j) (q + 2 * j) =
          T (q - (j + 1)) (q - (j + 1)) (q + 2 * j) := by
        obtain ⟨a, ha⟩ : ∃ a, q - j = a + 1 := ⟨q - (j + 1), by omega⟩
        have ha' : q - (j + 1) = a := by omega
        rw [ha, ha']
        have hfa := mul_T_fst a (a + 1) (q + 2 * j)
        have hfb := mul_T_snd a a (q + 2 * j)
        calc (((a + 1 : ℕ) : ℝ) ^ 2) * T (a + 1) (a + 1) (q + 2 * j)
            = ((a + 1 : ℕ) : ℝ) * (((a + 1 : ℕ) : ℝ) * T (a + 1) (a + 1) (q + 2 * j)) := by ring
          _ = ((a + 1 : ℕ) : ℝ) * T a (a + 1) (q + 2 * j) := by rw [hfa]
          _ = T a a (q + 2 * j) := hfb
      have hT2 : (((q + 2 * j + 1 : ℕ) : ℝ) * ((q + 2 * j + 2 : ℕ) : ℝ)) *
            T (q - (j + 1)) (q - (j + 1)) (q + 2 * j + 2) =
          T (q - (j + 1)) (q - (j + 1)) (q + 2 * j) := by
        have ht1 := mul_T_thd (q - (j + 1)) (q - (j + 1)) (q + 2 * j + 1)
        have ht2 := mul_T_thd (q - (j + 1)) (q - (j + 1)) (q + 2 * j)
        calc (((q + 2 * j + 1 : ℕ) : ℝ) * ((q + 2 * j + 2 : ℕ) : ℝ)) *
              T (q - (j + 1)) (q - (j + 1)) (q + 2 * j + 2)
            = ((q + 2 * j + 1 : ℕ) : ℝ) *
                (((q + 2 * j + 1 + 1 : ℕ) : ℝ) * T (q - (j + 1)) (q - (j + 1)) (q + 2 * j + 1 + 1)) := by ring
          _ = ((q + 2 * j + 1 : ℕ) : ℝ) * T (q - (j + 1)) (q - (j + 1)) (q + 2 * j + 1) := by rw [ht1]
          _ = T (q - (j + 1)) (q - (j + 1)) (q + 2 * j) := ht2
      have hden : ((q + 2 * j + 1 : ℕ) : ℝ) * ((q + 2 * j + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      have hT_eq : T (q - (j + 1)) (q - (j + 1)) (q + 2 * j + 2) =
          (((q - j : ℕ) : ℝ) ^ 2 / (((q + 2 * j + 1 : ℕ) : ℝ) * ((q + 2 * j + 2 : ℕ) : ℝ))) *
            T (q - j) (q - j) (q + 2 * j) := by
        rw [div_mul_eq_mul_div, eq_div_iff hden]
        linarith
      rw [hT_eq]; ring
    have hrat_le : (((q - j : ℕ) : ℝ) ^ 2 / (((q + 2 * j + 1 : ℕ) : ℝ) * ((q + 2 * j + 2 : ℕ) : ℝ))) ≤
        Real.exp (-((2 * (j : ℝ) + 1) / (3 * (q : ℝ)))) := by
      have h1 : (((q - j : ℕ) : ℝ) ^ 2 / (((q + 2 * j + 1 : ℕ) : ℝ) * ((q + 2 * j + 2 : ℕ) : ℝ))) ≤
          1 - (2 * (j : ℝ) + 1) / (3 * (q : ℝ)) := by
        have hc1 : ((q - j : ℕ) : ℝ) = (q : ℝ) - (j : ℝ) := by rw [Nat.cast_sub (by omega)]
        have hc2 : ((q + 2 * j + 1 : ℕ) : ℝ) = (q : ℝ) + 2 * (j : ℝ) + 1 := by push_cast; ring
        have hc3 : ((q + 2 * j + 2 : ℕ) : ℝ) = (q : ℝ) + 2 * (j : ℝ) + 2 := by push_cast; ring
        rw [hc1, hc2, hc3]
        have hden_pos : 0 < ((q : ℝ) + 2 * (j : ℝ) + 1) * ((q : ℝ) + 2 * (j : ℝ) + 2) := by positivity
        have hj_le : (j : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hk
        have hj_nn : (0 : ℝ) ≤ (j : ℝ) := by positivity
        rw [div_le_iff₀ hden_pos]
        have hden_ub : ((q : ℝ) + 2 * (j : ℝ) + 1) * ((q : ℝ) + 2 * (j : ℝ) + 2) ≤ 9 * (q : ℝ) ^ 2 := by
          nlinarith
        have hnum_lb : 3 * (q : ℝ) * (2 * (j : ℝ) + 1) ≤
            ((q : ℝ) + 2 * (j : ℝ) + 1) * ((q : ℝ) + 2 * (j : ℝ) + 2) - ((q : ℝ) - (j : ℝ)) ^ 2 := by
          nlinarith
        have hkey : (2 * (j : ℝ) + 1) / (3 * (q : ℝ)) *
            (((q : ℝ) + 2 * (j : ℝ) + 1) * ((q : ℝ) + 2 * (j : ℝ) + 2)) ≤
            3 * (q : ℝ) * (2 * (j : ℝ) + 1) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          have h2j1 : 0 ≤ 2 * (j : ℝ) + 1 := by positivity
          nlinarith
        linarith
      have h2 := Real.add_one_le_exp (-((2 * (j : ℝ) + 1) / (3 * (q : ℝ))))
      linarith
    have hrat_nn : 0 ≤ p3q q (q - j) / p3q q q := by
      refine div_nonneg ?_ (le_of_lt hp0)
      rw [p3q_eq_of_le (by omega)]
      have := T_pos (q - j) (q - j) (3 * q - 2 * (q - j))
      positivity
    rw [hstep]
    calc (((q - j : ℕ) : ℝ) ^ 2 / (((q + 2 * j + 1 : ℕ) : ℝ) * ((q + 2 * j + 2 : ℕ) : ℝ))) *
          (p3q q (q - j) / p3q q q)
        ≤ Real.exp (-((2 * (j : ℝ) + 1) / (3 * (q : ℝ)))) *
            Real.exp (-((j : ℝ) ^ 2) / (3 * (q : ℝ))) :=
          mul_le_mul hrat_le hih hrat_nn (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-(((j + 1 : ℕ) : ℝ) ^ 2) / (3 * (q : ℝ))) := by
          rw [← Real.exp_add]; congr 1; push_cast; ring

/-! ### Part 2: Cutoff `K_cut q = ⌊q^(5/8)⌋` and super-polynomial tail bounds -/

/-- Eighth root `q^(1/8)` used to define the local Gaussian cutoff `K_cut q = ⌊q^(5/8)⌋`. -/
noncomputable def w8 (q : ℕ) : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (q : ℝ)))

/-- Local cutoff index `⌊q^(5/8)⌋` separating the Gaussian core from super-polynomial tails. -/
@[nolint defsWithUnderscore]
noncomputable def K_cut (q : ℕ) : ℕ := Nat.floor (Real.sqrt (q : ℝ) * w8 q)

lemma w8_pos {q : ℕ} (hq : 1 ≤ q) : 0 < w8 q := by
  unfold w8; positivity

lemma w8_pow4 (q : ℕ) : (w8 q) ^ 4 = Real.sqrt (q : ℝ) := by
  unfold w8
  have h1 : (Real.sqrt (Real.sqrt (Real.sqrt (q : ℝ)))) ^ 2 = Real.sqrt (Real.sqrt (q : ℝ)) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h2 : (Real.sqrt (Real.sqrt (q : ℝ))) ^ 2 = Real.sqrt (q : ℝ) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  calc (Real.sqrt (Real.sqrt (Real.sqrt (q : ℝ)))) ^ 4
      = ((Real.sqrt (Real.sqrt (Real.sqrt (q : ℝ)))) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt (Real.sqrt (q : ℝ))) ^ 2 := by rw [h1]
    _ = Real.sqrt (q : ℝ) := h2

lemma w8_pow8 (q : ℕ) : (w8 q) ^ 8 = (q : ℝ) := by
  calc (w8 q) ^ 8 = ((w8 q) ^ 4) ^ 2 := by ring
    _ = (Real.sqrt (q : ℝ)) ^ 2 := by rw [w8_pow4]
    _ = (q : ℝ) := Real.sq_sqrt (by positivity)

lemma w8_ge_ten {q : ℕ} (hq : 10 ^ 8 ≤ q) : (10 : ℝ) ≤ w8 q := by
  have hqR : (10 : ℝ) ^ 8 ≤ (q : ℝ) := by exact_mod_cast hq
  rw [← w8_pow8 q] at hqR
  by_contra hlt
  push Not at hlt
  have hw0 : 0 ≤ w8 q := Real.sqrt_nonneg _
  have hlt8 : (w8 q) ^ 8 < (10 : ℝ) ^ 8 := pow_lt_pow_left₀ hlt hw0 (by norm_num)
  linarith

lemma K_cut_bounds {q : ℕ} (hq : 10 ^ 8 ≤ q) :
    (w8 q) ^ 5 - 1 < (K_cut q : ℝ) ∧ (K_cut q : ℝ) ≤ (w8 q) ^ 5 ∧ 1 ≤ K_cut q ∧ 2 * K_cut q < q := by
  have hw10 := w8_ge_ten hq
  have hw_eq : Real.sqrt (q : ℝ) * w8 q = (w8 q) ^ 5 := by
    rw [← w8_pow4 q]; ring
  have hlb : (w8 q) ^ 5 - 1 < (K_cut q : ℝ) := by
    unfold K_cut; rw [hw_eq]; exact Nat.sub_one_lt_floor _
  have hub : (K_cut q : ℝ) ≤ (w8 q) ^ 5 := by
    unfold K_cut; rw [hw_eq]; exact Nat.floor_le (by positivity)
  have hw5 : (100000 : ℝ) ≤ (w8 q) ^ 5 := by
    have : (10 : ℝ) ^ 5 ≤ (w8 q) ^ 5 := pow_le_pow_left₀ (by norm_num) hw10 5
    norm_num at this; exact this
  have h1 : 1 ≤ K_cut q := by
    have : (1 : ℝ) ≤ (K_cut q : ℝ) := by linarith
    exact_mod_cast this
  have h2K : 2 * K_cut q < q := by
    have hq8 := w8_pow8 q
    have hw3 : (1000 : ℝ) ≤ (w8 q) ^ 3 := by
      have : (10 : ℝ) ^ 3 ≤ (w8 q) ^ 3 := pow_le_pow_left₀ (by norm_num) hw10 3
      norm_num at this; exact this
    have hR : 2 * (K_cut q : ℝ) < (q : ℝ) := by
      have hmul : 2 * (w8 q) ^ 5 < (w8 q) ^ 8 := by
        have hpos5 : 0 < (w8 q) ^ 5 := by positivity
        nlinarith [show (w8 q) ^ 8 = (w8 q) ^ 5 * (w8 q) ^ 3 by ring]
      linarith
    exact_mod_cast hR
  exact ⟨hlb, hub, h1, h2K⟩

/-- Tail exponential decay for `k > K_cut q`. -/
lemma exp_tail_bound {q k : ℕ} (hq : 10 ^ 8 ≤ q) (hk : K_cut q < k) :
    Real.exp (-((k : ℝ) ^ 2) / (3 * (q : ℝ))) ≤
      ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) ^ 2 * Real.sqrt (q : ℝ)) := by
  have hw10 := w8_ge_ten hq
  have hw_pos : 0 < w8 q := by linarith
  have hw_eq : Real.sqrt (q : ℝ) * w8 q = (w8 q) ^ 5 := by rw [← w8_pow4 q]; ring
  have hk_gt : (w8 q) ^ 5 < (k : ℝ) := by
    unfold K_cut at hk
    rw [hw_eq] at hk
    exact (Nat.floor_lt (by positivity)).mp hk
  have hk2_ge : (w8 q) ^ 2 / 3 ≤ (k : ℝ) ^ 2 / (3 * (q : ℝ)) := by
    rw [← w8_pow8 q]
    have hsq : (w8 q) ^ 10 ≤ (k : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) (le_of_lt hk_gt) 2
      linarith [show ((w8 q) ^ 5) ^ 2 = (w8 q) ^ 10 by ring]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [show (w8 q) ^ 2 * (3 * (w8 q) ^ 8) = 3 * (w8 q) ^ 10 by ring]
  have hexp_le : Real.exp (-((k : ℝ) ^ 2) / (3 * (q : ℝ))) ≤ Real.exp (-((w8 q) ^ 2 / 3)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]; linarith
  have hfac := Real.pow_div_factorial_le_exp ((w8 q) ^ 2 / 3) (by positivity) 10
  have hpos_x : 0 < ((w8 q) ^ 2 / 3) ^ 10 := by positivity
  have hinv : Real.exp (-((w8 q) ^ 2 / 3)) ≤ (Nat.factorial 10 : ℝ) / ((w8 q) ^ 2 / 3) ^ 10 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) hpos_x]
    have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < (Nat.factorial 10 : ℝ))).mp hfac
    linarith
  have hden_eq : (Nat.factorial 10 : ℝ) / ((w8 q) ^ 2 / 3) ^ 10 =
      ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) ^ 2 * Real.sqrt (q : ℝ)) := by
    rw [← w8_pow4 q, ← w8_pow8 q, div_pow]
    have hne : (w8 q) ^ 20 ≠ 0 := by positivity
    have hpow : ((w8 q) ^ 2) ^ 10 = (w8 q) ^ 20 := by ring
    have hpow2 : ((w8 q) ^ 8) ^ 2 * (w8 q) ^ 4 = (w8 q) ^ 20 := by ring
    rw [hpow, hpow2]
    field_simp
  exact le_trans hexp_le (by rw [← hden_eq]; exact hinv)

/-- Euler-Maclaurin endpoint decay `exp(-K_cut q / sqrt q) ≤ C / q^2`. -/
lemma exp_cutoff_bound {q : ℕ} (hq : 10 ^ 8 ≤ q) :
    Real.exp (-((K_cut q : ℝ) * (1 / Real.sqrt (q : ℝ)))) ≤
      ((Nat.factorial 16 : ℝ) * 2 ^ 16) / (q : ℝ) ^ 2 := by
  have hw10 := w8_ge_ten hq
  have hw_pos : 0 < w8 q := by linarith
  have hK := (K_cut_bounds hq).1
  have hM_ge : w8 q / 2 ≤ (K_cut q : ℝ) * (1 / Real.sqrt (q : ℝ)) := by
    rw [← w8_pow4 q, mul_one_div, le_div_iff₀ (by positivity)]
    have hw4 : (10000 : ℝ) ≤ (w8 q) ^ 4 := by
      have : (10 : ℝ) ^ 4 ≤ (w8 q) ^ 4 := pow_le_pow_left₀ (by norm_num) hw10 4
      norm_num at this; exact this
    have hw5 : (w8 q) ^ 5 / 2 ≤ (w8 q) ^ 5 - 1 := by
      have : (2 : ℝ) ≤ (w8 q) ^ 5 := by nlinarith
      linarith
    nlinarith [show w8 q / 2 * (w8 q) ^ 4 = (w8 q) ^ 5 / 2 by ring]
  have hexp_le : Real.exp (-((K_cut q : ℝ) * (1 / Real.sqrt (q : ℝ)))) ≤ Real.exp (-(w8 q / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hfac := Real.pow_div_factorial_le_exp (w8 q / 2) (by positivity) 16
  have hpos_x : 0 < (w8 q / 2) ^ 16 := by positivity
  have hinv : Real.exp (-(w8 q / 2)) ≤ (Nat.factorial 16 : ℝ) / (w8 q / 2) ^ 16 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) hpos_x]
    have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < (Nat.factorial 16 : ℝ))).mp hfac
    linarith
  have hden_eq : (Nat.factorial 16 : ℝ) / (w8 q / 2) ^ 16 =
      ((Nat.factorial 16 : ℝ) * 2 ^ 16) / (q : ℝ) ^ 2 := by
    rw [← w8_pow8 q, div_pow]
    have hne : (w8 q) ^ 16 ≠ 0 := by positivity
    have hpow : ((w8 q) ^ 8) ^ 2 = (w8 q) ^ 16 := by ring
    rw [hpow]
    field_simp
  exact le_trans hexp_le (by rw [← hden_eq]; exact hinv)

/-! ### Part 3: 5-term logarithm Taylor bound on `[-1/2, 1/2]` -/

/-- Five-term Taylor polynomial of `log (1 + v)` on `[-1/2, 1/2]`. -/
noncomputable def logPoly5 (v : ℝ) : ℝ :=
  v - v ^ 2 / 2 + v ^ 3 / 3 - v ^ 4 / 4 + v ^ 5 / 5

lemma abs_log_one_add_sub_logPoly5_le {v : ℝ} (hv : |v| ≤ 1 / 2) :
    |Real.log (1 + v) - logPoly5 v| ≤ 2 * v ^ 6 := by
  let f : ℝ → ℝ := fun t => Real.log (1 + t) - logPoly5 t
  have hf0 : f 0 = 0 := by simp [f, logPoly5]
  have hf_deriv : ∀ t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
      HasDerivAt f (-(t ^ 5 / (1 + t))) t := by
    intro t ht
    have h1t : 1 + t ≠ 0 := by linarith [ht.1]
    have hlog : HasDerivAt (fun u => Real.log (1 + u)) (1 / (1 + t)) t := by
      have h1 : HasDerivAt (fun u => 1 + u) 1 t := (hasDerivAt_id t).const_add 1
      have h2 := h1.log h1t
      convert h2 using 1
    have hpoly : HasDerivAt logPoly5 (1 - t + t ^ 2 - t ^ 3 + t ^ 4) t := by
      have d1 := hasDerivAt_id t
      have d2 := (hasDerivAt_pow 2 t).div_const 2
      have d3 := (hasDerivAt_pow 3 t).div_const 3
      have d4 := (hasDerivAt_pow 4 t).div_const 4
      have d5 := (hasDerivAt_pow 5 t).div_const 5
      have h := (((d1.sub d2).add d3).sub d4).add d5
      have heq : ((((id - fun x : ℝ => x ^ 2 / 2) + fun x : ℝ => x ^ 3 / 3) -
          fun x : ℝ => x ^ 4 / 4) + fun x : ℝ => x ^ 5 / 5) = logPoly5 := by
        ext x; unfold logPoly5; simp [Pi.add_apply, Pi.sub_apply]
      rw [heq] at h
      convert h using 1; norm_num
    have hd := hlog.sub hpoly
    convert hd using 1
    field_simp; ring
  have h1 : ∀ t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
      HasDerivAt (fun u => 2 * u ^ 6 - f u) (12 * t ^ 5 + t ^ 5 / (1 + t)) t := by
    intro t ht
    have hd := ((hasDerivAt_pow 6 t).const_mul (2 : ℝ)).sub (hf_deriv t ht)
    convert hd using 1; ring
  have h2 : ∀ t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
      HasDerivAt (fun u => 2 * u ^ 6 + f u) (12 * t ^ 5 - t ^ 5 / (1 + t)) t := by
    intro t ht
    have hd := ((hasDerivAt_pow 6 t).const_mul (2 : ℝ)).add (hf_deriv t ht)
    convert hd using 1; ring
  have hv_mem : v ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := abs_le.mp hv
  rw [abs_le]
  by_cases hv0 : 0 ≤ v
  · have hmono1 : MonotoneOn (fun u => 2 * u ^ 6 - f u) (Set.Icc 0 (1 / 2)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
      · exact fun t ht => (h1 t ⟨by linarith [ht.1], ht.2⟩).continuousAt.continuousWithinAt
      · exact fun t ht => (h1 t ⟨by linarith [(interior_subset ht).1], (interior_subset ht).2⟩).differentiableAt.differentiableWithinAt
      · intro t ht
        have hm := interior_subset ht
        rw [(h1 t ⟨by linarith [hm.1], hm.2⟩).deriv]
        have ht0 : 0 ≤ t := hm.1
        have h1t : 0 < 1 + t := by linarith
        positivity
    have hmono2 : MonotoneOn (fun u => 2 * u ^ 6 + f u) (Set.Icc 0 (1 / 2)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
      · exact fun t ht => (h2 t ⟨by linarith [ht.1], ht.2⟩).continuousAt.continuousWithinAt
      · exact fun t ht => (h2 t ⟨by linarith [(interior_subset ht).1], (interior_subset ht).2⟩).differentiableAt.differentiableWithinAt
      · intro t ht
        have hm := interior_subset ht
        rw [(h2 t ⟨by linarith [hm.1], hm.2⟩).deriv]
        have ht0 : 0 ≤ t := hm.1
        have h1t : 1 ≤ 1 + t := by linarith
        have hdiv : t ^ 5 / (1 + t) ≤ t ^ 5 := div_le_self (by positivity) h1t
        have ht5 : 0 ≤ t ^ 5 := by positivity
        linarith
    have hg1 := hmono1 (Set.left_mem_Icc.mpr (by norm_num)) ⟨hv0, hv_mem.2⟩ hv0
    have hg2 := hmono2 (Set.left_mem_Icc.mpr (by norm_num)) ⟨hv0, hv_mem.2⟩ hv0
    simp only [hf0, zero_pow (by norm_num : 6 ≠ 0), mul_zero, sub_zero, add_zero] at hg1 hg2
    exact ⟨by linarith, by linarith⟩
  · push Not at hv0
    have hanti1 : AntitoneOn (fun u => 2 * u ^ 6 - f u) (Set.Icc (-(1 / 2)) 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc (-(1 / 2)) 0) ?_ ?_ ?_
      · exact fun t ht => (h1 t ⟨ht.1, by linarith [ht.2]⟩).continuousAt.continuousWithinAt
      · exact fun t ht => (h1 t ⟨(interior_subset ht).1, by linarith [(interior_subset ht).2]⟩).differentiableAt.differentiableWithinAt
      · intro t ht
        have hm := interior_subset ht
        rw [(h1 t ⟨hm.1, by linarith [hm.2]⟩).deriv]
        have ht0 : t ≤ 0 := hm.2
        have h1t : 0 < 1 + t := by linarith [hm.1]
        have ht5 : t ^ 5 ≤ 0 := by
          have : t ^ 4 ≥ 0 := by positivity
          nlinarith [show t ^ 5 = t ^ 4 * t by ring]
        have hdiv : t ^ 5 / (1 + t) ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht5 (le_of_lt h1t)
        linarith
    have hanti2 : AntitoneOn (fun u => 2 * u ^ 6 + f u) (Set.Icc (-(1 / 2)) 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc (-(1 / 2)) 0) ?_ ?_ ?_
      · exact fun t ht => (h2 t ⟨ht.1, by linarith [ht.2]⟩).continuousAt.continuousWithinAt
      · exact fun t ht => (h2 t ⟨(interior_subset ht).1, by linarith [(interior_subset ht).2]⟩).differentiableAt.differentiableWithinAt
      · intro t ht
        have hm := interior_subset ht
        rw [(h2 t ⟨hm.1, by linarith [hm.2]⟩).deriv]
        have ht0 : t ≤ 0 := hm.2
        have h1t : 1 / 2 ≤ 1 + t := by linarith [hm.1]
        have ht5 : t ^ 5 ≤ 0 := by
          have : t ^ 4 ≥ 0 := by positivity
          nlinarith [show t ^ 5 = t ^ 4 * t by ring]
        have hdiv : -(t ^ 5 / (1 + t)) ≤ -(2 * t ^ 5) := by
          rw [neg_le_neg_iff, le_div_iff₀ (by linarith)]
          nlinarith
        linarith
    have hg1 := hanti1 ⟨hv_mem.1, le_of_lt hv0⟩ (Set.right_mem_Icc.mpr (by norm_num)) (le_of_lt hv0)
    have hg2 := hanti2 ⟨hv_mem.1, le_of_lt hv0⟩ (Set.right_mem_Icc.mpr (by norm_num)) (le_of_lt hv0)
    simp only [hf0, zero_pow (by norm_num : 6 ≠ 0), mul_zero, sub_zero, add_zero] at hg1 hg2
    exact ⟨by linarith, by linarith⟩

/-! ### Part 4: Local logarithmic and exponential ratio expansion -/

/-- Cubic local log-ratio perturbation polynomial in `(t, ε)`. -/
@[nolint defsWithUnderscore]
noncomputable def R_approx (t ε : ℝ) : ℝ :=
  -ε * t ^ 3 + ε ^ 2 * (-(3 / 2 : ℝ) * t ^ 4 + (3 / 2 : ℝ) * t ^ 2) +
    ε ^ 3 * (-(3 / 2 : ℝ) * t ^ 5 + t ^ 3)

/-- Cubic Taylor polynomial `1 + x + x^2/2 + x^3/6` of `exp x`. -/
noncomputable def T3 (x : ℝ) : ℝ := 1 + x + x ^ 2 / 2 + x ^ 3 / 6

/-- Elementary Lipschitz bound for `exp` on `(-∞, 1]`: `|exp a - exp b| ≤ 3 * |a - b|`. -/
lemma abs_exp_sub_exp_le {a b : ℝ} (ha : a ≤ 1) (hb : b ≤ 1) :
    |Real.exp a - Real.exp b| ≤ 3 * |a - b| := by
  have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  by_cases hba : b ≤ a
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hba)),
        abs_of_nonneg (sub_nonneg.mpr hba)]
    have hfact : Real.exp a - Real.exp b = Real.exp a * (1 - Real.exp (-(a - b))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]; congr 2; ring
    have h1 : 1 - Real.exp (-(a - b)) ≤ a - b := by
      linarith [Real.add_one_le_exp (-(a - b))]
    have h2 : Real.exp a ≤ 3 := le_trans (Real.exp_le_exp.mpr ha) he1
    rw [hfact]
    have hnn : 0 ≤ 1 - Real.exp (-(a - b)) := by
      have : Real.exp (-(a - b)) ≤ 1 := by
        rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos a)))
      (mul_le_mul_of_nonneg_right h2 (by linarith))
  · push Not at hba
    rw [abs_sub_comm (Real.exp a), abs_sub_comm a]
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (le_of_lt hba))),
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt hba))]
    have hfact : Real.exp b - Real.exp a = Real.exp b * (1 - Real.exp (-(b - a))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]; congr 2; ring
    have h1 : 1 - Real.exp (-(b - a)) ≤ b - a := by
      linarith [Real.add_one_le_exp (-(b - a))]
    have h2 : Real.exp b ≤ 3 := le_trans (Real.exp_le_exp.mpr hb) he1
    rw [hfact]
    exact le_trans (mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos b)))
      (mul_le_mul_of_nonneg_right h2 (by linarith))

/-- Elementary power domination: for any `x : ℝ` and `m ≤ n`, `|x|^m ≤ 1 + |x|^n`. -/
lemma abs_pow_le_one_add {x : ℝ} {m n : ℕ} (hmn : m ≤ n) :
    |x| ^ m ≤ 1 + |x| ^ n := by
  by_cases h1 : |x| ≤ 1
  · have := pow_le_one₀ (abs_nonneg x) h1 (n := m)
    have : 0 ≤ |x| ^ n := by positivity
    linarith
  · push Not at h1
    have := pow_le_pow_right₀ (le_of_lt h1) hmn
    linarith

private lemma stirling_diff_bound {q m1 m2 : ℕ} {u : ℝ} (hq : 1 ≤ q) (hu : |u| ≤ 1 / 4)
    (hm1 : (m1 : ℝ) = (q : ℝ) * (1 + u)) (hm2 : (m2 : ℝ) = (q : ℝ) * (1 - 2 * u)) :
    let ε := 1 / Real.sqrt (q : ℝ)
    let t := u / ε
    |3 * stirlingRem q - 2 * stirlingRem m1 - stirlingRem m2| ≤ 4 * ε ^ 4 * (1 + t ^ 6) := by
  intro ε t
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hsqq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
  have hε_pos : 0 < ε := by dsimp only [ε]; positivity
  have hε_le1 : ε ≤ 1 := by
    dsimp only [ε]; rw [div_le_one hsqq]
    have : Real.sqrt 1 ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt hqR
    simpa using this
  have hε2 : ε ^ 2 = 1 / (q : ℝ) := by
    dsimp only [ε]; rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hqpos)]
  have hu_eq : u = ε * t := by dsimp only [t]; field_simp
  have hu_bounds := abs_le.mp hu
  have h1u_lb : 3 / 4 ≤ 1 + u := by linarith
  have h12u_lb : 1 / 2 ≤ 1 - 2 * u := by linarith
  have hm1_ge1 : 1 ≤ m1 := by
    have : (0 : ℝ) < (m1 : ℝ) := by rw [hm1]; exact mul_pos hqpos (by linarith)
    have : 0 < m1 := by exact_mod_cast this
    omega
  have hm2_ge1 : 1 ≤ m2 := by
    have : (0 : ℝ) < (m2 : ℝ) := by rw [hm2]; exact mul_pos hqpos (by linarith)
    have : 0 < m2 := by exact_mod_cast this
    omega
  set Δst := 3 * stirlingRem q - 2 * stirlingRem m1 - stirlingRem m2
  obtain ⟨hlq, huq⟩ := stirlingRem_bounds q hq
  obtain ⟨hl1, hu1⟩ := stirlingRem_bounds m1 hm1_ge1
  obtain ⟨hl2, hu2⟩ := stirlingRem_bounds m2 hm2_ge1
  set mainSt := 3 / (12 * (q : ℝ)) - 2 / (12 * (m1 : ℝ)) - 1 / (12 * (m2 : ℝ))
  have hmainSt_eq : mainSt = -(u ^ 2 / (2 * (q : ℝ) * (1 + u) * (1 - 2 * u))) := by
    dsimp only [mainSt]; rw [hm1, hm2]
    have h1 : (1 + u) ≠ 0 := by linarith
    have h2 : (1 - 2 * u) ≠ 0 := by linarith
    field_simp; ring
  have hmainSt_abs : |mainSt| ≤ 2 * ε ^ 4 * (1 + t ^ 6) := by
    rw [hmainSt_eq, abs_neg, abs_of_nonneg (by positivity)]
    have hprod : 3 / 8 ≤ (1 + u) * (1 - 2 * u) :=
      le_trans (by norm_num) (mul_le_mul h1u_lb h12u_lb (by norm_num) (by linarith))
    have hu2_div : u ^ 2 / (2 * (q : ℝ) * (1 + u) * (1 - 2 * u)) ≤ (4 / 3 : ℝ) * (u ^ 2 / (q : ℝ)) := by
      rw [div_le_iff₀ (by positivity)]
      have : (4 / 3 : ℝ) * (u ^ 2 / (q : ℝ)) * (2 * (q : ℝ) * (1 + u) * (1 - 2 * u)) =
          u ^ 2 * ((8 / 3 : ℝ) * ((1 + u) * (1 - 2 * u))) := by field_simp; ring
      rw [this]
      exact le_mul_of_one_le_right (sq_nonneg u) (by linarith)
    have hrewrite : u ^ 2 / (q : ℝ) = ε ^ 4 * t ^ 2 := by
      rw [hu_eq, mul_pow, div_eq_mul_inv, show (q : ℝ)⁻¹ = ε ^ 2 by rw [hε2, one_div]]; ring
    have ht2_le : t ^ 2 ≤ 1 + t ^ 6 := by
      have := abs_pow_le_one_add (x := t) (m := 2) (n := 6) (by omega)
      simpa [sq_abs, show |t| ^ 6 = t ^ 6 by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, sq_abs, ← pow_mul]] using this
    rw [hrewrite] at hu2_div
    have hmul := mul_le_mul_of_nonneg_left ht2_le (by positivity : 0 ≤ ε ^ 4)
    have hε4_nn : 0 ≤ ε ^ 4 * (1 + t ^ 6) := by positivity
    linarith
  have hremSt_abs : |Δst - mainSt| ≤ 2 * ε ^ 4 * (1 + t ^ 6) := by
    have hlb : -(3 / (15 * (q : ℝ) ^ 3)) ≤ Δst - mainSt := by
      dsimp only [Δst, mainSt]
      have hq3 : 3 * (1 / (12 * (q : ℝ))) = 3 / (12 * (q : ℝ)) := by ring
      have hq3' : 3 * (1 / (15 * (q : ℝ) ^ 3)) = 3 / (15 * (q : ℝ) ^ 3) := by ring
      have hm12 : 2 * (1 / (12 * (m1 : ℝ))) = 2 / (12 * (m1 : ℝ)) := by ring
      linarith
    have hub : Δst - mainSt ≤ 2 / (15 * (m1 : ℝ) ^ 3) + 1 / (15 * (m2 : ℝ) ^ 3) := by
      dsimp only [Δst, mainSt]
      have hq3 : 3 * (1 / (12 * (q : ℝ))) = 3 / (12 * (q : ℝ)) := by ring
      have hm12 : 2 * (1 / (12 * (m1 : ℝ))) = 2 / (12 * (m1 : ℝ)) := by ring
      have hm15 : 2 * (1 / (15 * (m1 : ℝ) ^ 3)) = 2 / (15 * (m1 : ℝ) ^ 3) := by ring
      linarith
    have hm1_lb : (q : ℝ) / 2 ≤ (m1 : ℝ) := by
      rw [hm1]; exact le_trans (by linarith) (mul_le_mul_of_nonneg_left h1u_lb (le_of_lt hqpos))
    have hm2_lb : (q : ℝ) / 2 ≤ (m2 : ℝ) := by
      rw [hm2]; exact le_trans (by linarith) (mul_le_mul_of_nonneg_left h12u_lb (le_of_lt hqpos))
    have hm1_cube : (q : ℝ) ^ 3 / 8 ≤ (m1 : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) hm1_lb 3
      linarith [show ((q : ℝ) / 2) ^ 3 = (q : ℝ) ^ 3 / 8 by ring]
    have hm2_cube : (q : ℝ) ^ 3 / 8 ≤ (m2 : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) hm2_lb 3
      linarith [show ((q : ℝ) / 2) ^ 3 = (q : ℝ) ^ 3 / 8 by ring]
    have h1_le : 2 / (15 * (m1 : ℝ) ^ 3) ≤ 16 / (15 * (q : ℝ) ^ 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have h2_le : 1 / (15 * (m2 : ℝ) ^ 3) ≤ 8 / (15 * (q : ℝ) ^ 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have hsum16 : 16 / (15 * (q : ℝ) ^ 3) + 8 / (15 * (q : ℝ) ^ 3) = 24 / (15 * (q : ℝ) ^ 3) := by ring
    have hcube : 1 / (q : ℝ) ^ 3 ≤ ε ^ 4 := by
      have hq3 : 1 / (q : ℝ) ^ 3 = ε ^ 6 := by
        rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, hε2, one_div_pow]
      rw [hq3]
      have hε2_le : ε ^ 2 ≤ 1 := pow_le_one₀ (le_of_lt hε_pos) hε_le1 (n := 2)
      rw [show ε ^ 6 = ε ^ 4 * ε ^ 2 by ring]
      exact mul_le_of_le_one_right (by positivity) hε2_le
    have h24 : 24 / (15 * (q : ℝ) ^ 3) ≤ 2 * ε ^ 4 := by
      have : 24 / (15 * (q : ℝ) ^ 3) = (24 / 15 : ℝ) * (1 / (q : ℝ) ^ 3) := by ring
      have hnn : 0 ≤ 1 / (q : ℝ) ^ 3 := by positivity
      linarith
    have h3_le : 3 / (15 * (q : ℝ) ^ 3) ≤ 2 * ε ^ 4 := by
      have : 3 / (15 * (q : ℝ) ^ 3) = (3 / 15 : ℝ) * (1 / (q : ℝ) ^ 3) := by ring
      have hnn : 0 ≤ 1 / (q : ℝ) ^ 3 := by positivity
      linarith
    have h2ε : 2 * ε ^ 4 ≤ 2 * ε ^ 4 * (1 + t ^ 6) :=
      le_mul_of_one_le_right (by positivity) (by linarith [show (0 : ℝ) ≤ t ^ 6 by positivity])
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hsplit : Δst = mainSt + (Δst - mainSt) := by ring
  rw [hsplit]
  exact le_trans (abs_add_le mainSt (Δst - mainSt)) (by linarith)

/-- Unified local log-ratio expansion for both `q + k` (`u = k/q`) and `q - k` (`u = -k/q`). -/
lemma log_ratio_approx {q m1 m2 : ℕ} {u : ℝ} (hq : 1 ≤ q) (hu : |u| ≤ 1 / 4)
    (hm1 : (m1 : ℝ) = (q : ℝ) * (1 + u)) (hm2 : (m2 : ℝ) = (q : ℝ) * (1 - 2 * u)) :
    let ε := 1 / Real.sqrt (q : ℝ)
    let t := u / ε
    |Real.log (((q.factorial : ℝ) ^ 3) / ((m1.factorial : ℝ) ^ 2 * (m2.factorial : ℝ))) -
        (-3 * t ^ 2 + R_approx t ε)| ≤ 300 * ε ^ 4 * (1 + t ^ 6) := by
  intro ε t
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hsqq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
  have hε_pos : 0 < ε := by dsimp only [ε]; positivity
  have hε_le1 : ε ≤ 1 := by
    dsimp only [ε]
    rw [div_le_one hsqq]
    have : Real.sqrt 1 ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt hqR
    simpa using this
  have hε2 : ε ^ 2 = 1 / (q : ℝ) := by
    dsimp only [ε]; rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hqpos)]
  have hu_eq : u = ε * t := by
    dsimp only [t]; field_simp
  have hqu2 : (q : ℝ) * u ^ 2 = t ^ 2 := by
    rw [hu_eq, mul_pow, ← mul_assoc, show (q : ℝ) * ε ^ 2 = 1 by rw [hε2]; field_simp, one_mul]
  have hqu_pow : ∀ k : ℕ, (q : ℝ) * u ^ (k + 2) = ε ^ k * t ^ (k + 2) := by
    intro k
    rw [hu_eq, mul_pow, pow_add, pow_add]
    have h1 : (q : ℝ) * ε ^ 2 = 1 := by rw [hε2]; field_simp
    calc (q : ℝ) * (ε ^ k * ε ^ 2 * (t ^ k * t ^ 2))
        = ((q : ℝ) * ε ^ 2) * (ε ^ k * (t ^ k * t ^ 2)) := by ring
      _ = ε ^ k * (t ^ k * t ^ 2) := by rw [h1, one_mul]
  have hu_bounds := abs_le.mp hu
  have h1u_lb : 3 / 4 ≤ 1 + u := by linarith
  have h1u_ub : 1 + u ≤ 5 / 4 := by linarith
  have h12u_lb : 1 / 2 ≤ 1 - 2 * u := by linarith
  have h12u_ub : 1 - 2 * u ≤ 3 / 2 := by linarith
  -- Exact decomposition via stirlingRem
  have hlog_id :
      Real.log (((q.factorial : ℝ) ^ 3) / ((m1.factorial : ℝ) ^ 2 * (m2.factorial : ℝ))) =
        -2 * ((q : ℝ) * (1 + u) + 1 / 2) * Real.log (1 + u) -
        ((q : ℝ) * (1 - 2 * u) + 1 / 2) * Real.log (1 - 2 * u) +
        (3 * stirlingRem q - 2 * stirlingRem m1 - stirlingRem m2) := by
    rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
    have hlm1 : Real.log (m1 : ℝ) = Real.log (q : ℝ) + Real.log (1 + u) := by
      rw [hm1, Real.log_mul (ne_of_gt hqpos) (by linarith)]
    have hlm2 : Real.log (m2 : ℝ) = Real.log (q : ℝ) + Real.log (1 - 2 * u) := by
      rw [hm2, Real.log_mul (ne_of_gt hqpos) (by linarith)]
    unfold stirlingRem
    rw [hlm1, hlm2, hm1, hm2]
    push_cast; ring
  set Δst := 3 * stirlingRem q - 2 * stirlingRem m1 - stirlingRem m2
  have hΔst : |Δst| ≤ 4 * ε ^ 4 * (1 + t ^ 6) := stirling_diff_bound hq hu hm1 hm2
  -- Expand log(1+u) and log(1-2u) using logPoly5
  set e1 := Real.log (1 + u) - logPoly5 u
  set e2 := Real.log (1 - 2 * u) - logPoly5 (-2 * u)
  have he1 : |e1| ≤ 2 * u ^ 6 := abs_log_one_add_sub_logPoly5_le (by linarith)
  have he2 : |e2| ≤ 128 * u ^ 6 := by
    have h := abs_log_one_add_sub_logPoly5_le (v := -2 * u) (by
      rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith)
    have hrew : 1 + -2 * u = 1 - 2 * u := by ring
    have hpow : 2 * (-2 * u) ^ 6 = 128 * u ^ 6 := by ring
    rw [hrew, hpow] at h
    exact h
  -- Exact polynomial identity for the logPoly5 terms
  have hpoly_id :
      -2 * ((q : ℝ) * (1 + u) + 1 / 2) * logPoly5 u -
        ((q : ℝ) * (1 - 2 * u) + 1 / 2) * logPoly5 (-2 * u) -
        (-3 * t ^ 2 + R_approx t ε) =
      -(66 / 5 : ℝ) * (ε ^ 4 * t ^ 6) + (9 / 4 : ℝ) * (ε ^ 4 * t ^ 4) + 3 * (ε ^ 5 * t ^ 5) := by
    have hq3 := hqu_pow 1
    have hq4 := hqu_pow 2
    have hq5 := hqu_pow 3
    have hq6 := hqu_pow 4
    have hu2 : u ^ 2 = ε ^ 2 * t ^ 2 := by rw [hu_eq, mul_pow]
    have hu3 : u ^ 3 = ε ^ 3 * t ^ 3 := by rw [hu_eq, mul_pow]
    have hu4 : u ^ 4 = ε ^ 4 * t ^ 4 := by rw [hu_eq, mul_pow]
    have hu5 : u ^ 5 = ε ^ 5 * t ^ 5 := by rw [hu_eq, mul_pow]
    have hexpand :
        -2 * ((q : ℝ) * (1 + u) + 1 / 2) * logPoly5 u -
          ((q : ℝ) * (1 - 2 * u) + 1 / 2) * logPoly5 (-2 * u) =
        -3 * ((q : ℝ) * u ^ 2) - ((q : ℝ) * u ^ 3) -
          (3 / 2 : ℝ) * ((q : ℝ) * u ^ 4) + (3 / 2 : ℝ) * u ^ 2 -
          (3 / 2 : ℝ) * ((q : ℝ) * u ^ 5) + u ^ 3 -
          (66 / 5 : ℝ) * ((q : ℝ) * u ^ 6) + (9 / 4 : ℝ) * u ^ 4 + 3 * u ^ 5 := by
      unfold logPoly5; ring
    rw [hexpand, hqu2, hq3, hq4, hq5, hq6, hu2, hu3, hu4, hu5]
    unfold R_approx; ring
  have hpoly_tail : |-(66 / 5 : ℝ) * (ε ^ 4 * t ^ 6) + (9 / 4 : ℝ) * (ε ^ 4 * t ^ 4) + 3 * (ε ^ 5 * t ^ 5)| ≤
      20 * ε ^ 4 * (1 + t ^ 6) := by
    have ht4 : t ^ 4 ≤ 1 + t ^ 6 := by
      have := abs_pow_le_one_add (x := t) (m := 4) (n := 6) (by omega)
      simpa [show |t| ^ 4 = t ^ 4 by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul],
             show |t| ^ 6 = t ^ 6 by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, sq_abs, ← pow_mul]] using this
    have ht5 : |t| ^ 5 ≤ 1 + t ^ 6 := by
      have := abs_pow_le_one_add (x := t) (m := 5) (n := 6) (by omega)
      simpa [show |t| ^ 6 = t ^ 6 by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, sq_abs, ← pow_mul]] using this
    have htri : |-(66 / 5 : ℝ) * (ε ^ 4 * t ^ 6) + (9 / 4 : ℝ) * (ε ^ 4 * t ^ 4) + 3 * (ε ^ 5 * t ^ 5)| ≤
        |-(66 / 5 : ℝ) * (ε ^ 4 * t ^ 6)| + |(9 / 4 : ℝ) * (ε ^ 4 * t ^ 4)| + |3 * (ε ^ 5 * t ^ 5)| := by
      linarith [abs_add_le (-(66 / 5 : ℝ) * (ε ^ 4 * t ^ 6) + (9 / 4 : ℝ) * (ε ^ 4 * t ^ 4)) (3 * (ε ^ 5 * t ^ 5)),
                abs_add_le (-(66 / 5 : ℝ) * (ε ^ 4 * t ^ 6)) ((9 / 4 : ℝ) * (ε ^ 4 * t ^ 4))]
    have ha : |-(66 / 5 : ℝ) * (ε ^ 4 * t ^ 6)| = (66 / 5 : ℝ) * (ε ^ 4 * t ^ 6) := by
      rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 66 / 5), abs_of_nonneg (by positivity)]
    have hb : |(9 / 4 : ℝ) * (ε ^ 4 * t ^ 4)| = (9 / 4 : ℝ) * (ε ^ 4 * t ^ 4) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 4), abs_of_nonneg (by positivity)]
    have hc : |3 * (ε ^ 5 * t ^ 5)| ≤ 3 * (ε ^ 4 * (1 + t ^ 6)) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos (by positivity : 0 < ε ^ 5), abs_pow]
      have hε5 : ε ^ 5 ≤ ε ^ 4 := by
        rw [show ε ^ 5 = ε ^ 4 * ε by ring]; exact mul_le_of_le_one_right (by positivity) hε_le1
      have hmul := mul_le_mul hε5 ht5 (by positivity) (by positivity)
      linarith
    have hm_t4 : ε ^ 4 * t ^ 4 ≤ ε ^ 4 * (1 + t ^ 6) := mul_le_mul_of_nonneg_left ht4 (by positivity)
    have hm_t6 : ε ^ 4 * t ^ 6 ≤ ε ^ 4 * (1 + t ^ 6) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hnn : 0 ≤ ε ^ 4 * (1 + t ^ 6) := by positivity
    linarith
  have hlog_err : |-2 * ((q : ℝ) * (1 + u) + 1 / 2) * e1 - ((q : ℝ) * (1 - 2 * u) + 1 / 2) * e2| ≤
      264 * ε ^ 4 * (1 + t ^ 6) := by
    have hc1_pos : 0 < (q : ℝ) * (1 + u) + 1 / 2 := by
      have : 0 < (q : ℝ) * (1 + u) := mul_pos hqpos (by linarith); linarith
    have hc2_pos : 0 < (q : ℝ) * (1 - 2 * u) + 1 / 2 := by
      have : 0 < (q : ℝ) * (1 - 2 * u) := mul_pos hqpos (by linarith); linarith
    have hc1_ub : 2 * ((q : ℝ) * (1 + u) + 1 / 2) ≤ 4 * (q : ℝ) := by
      have := mul_le_mul_of_nonneg_left h1u_ub (le_of_lt hqpos); linarith
    have hc2_ub : (q : ℝ) * (1 - 2 * u) + 1 / 2 ≤ 2 * (q : ℝ) := by
      have := mul_le_mul_of_nonneg_left h12u_ub (le_of_lt hqpos); linarith
    have h1 : |-2 * ((q : ℝ) * (1 + u) + 1 / 2) * e1| ≤ 8 * ((q : ℝ) * u ^ 6) := by
      rw [show -2 * ((q : ℝ) * (1 + u) + 1 / 2) * e1 = -(2 * ((q : ℝ) * (1 + u) + 1 / 2)) * e1 by ring,
          abs_mul, abs_neg, abs_of_pos (by linarith)]
      have hmul := mul_le_mul hc1_ub he1 (abs_nonneg e1) (by positivity)
      linarith [show 4 * (q : ℝ) * (2 * u ^ 6) = 8 * ((q : ℝ) * u ^ 6) by ring]
    have h2 : |((q : ℝ) * (1 - 2 * u) + 1 / 2) * e2| ≤ 256 * ((q : ℝ) * u ^ 6) := by
      rw [abs_mul, abs_of_pos hc2_pos]
      have hmul := mul_le_mul hc2_ub he2 (abs_nonneg e2) (by positivity)
      linarith [show 2 * (q : ℝ) * (128 * u ^ 6) = 256 * ((q : ℝ) * u ^ 6) by ring]
    have hqu6 : (q : ℝ) * u ^ 6 = ε ^ 4 * t ^ 6 := hqu_pow 4
    have htri := abs_sub (-2 * ((q : ℝ) * (1 + u) + 1 / 2) * e1) (((q : ℝ) * (1 - 2 * u) + 1 / 2) * e2)
    have hε4_nn : 0 ≤ ε ^ 4 := by positivity
    linarith [show 264 * ε ^ 4 * (1 + t ^ 6) = 264 * ε ^ 4 + 264 * (ε ^ 4 * t ^ 6) by ring]
  have htotal :
      Real.log (((q.factorial : ℝ) ^ 3) / ((m1.factorial : ℝ) ^ 2 * (m2.factorial : ℝ))) -
        (-3 * t ^ 2 + R_approx t ε) =
      (-2 * ((q : ℝ) * (1 + u) + 1 / 2) * logPoly5 u -
        ((q : ℝ) * (1 - 2 * u) + 1 / 2) * logPoly5 (-2 * u) - (-3 * t ^ 2 + R_approx t ε)) +
      (-2 * ((q : ℝ) * (1 + u) + 1 / 2) * e1 - ((q : ℝ) * (1 - 2 * u) + 1 / 2) * e2) + Δst := by
    rw [hlog_id]
    dsimp only [e1, e2, Δst]
    ring
  rw [htotal, hpoly_id]
  set P1 := -(66 / 5 : ℝ) * (ε ^ 4 * t ^ 6) + (9 / 4 : ℝ) * (ε ^ 4 * t ^ 4) + 3 * (ε ^ 5 * t ^ 5)
  set P2 := -2 * ((q : ℝ) * (1 + u) + 1 / 2) * e1 - ((q : ℝ) * (1 - 2 * u) + 1 / 2) * e2
  have htri : |P1 + P2 + Δst| ≤ |P1| + |P2| + |Δst| := by
    linarith [abs_add_le (P1 + P2) Δst, abs_add_le P1 P2]
  have hnn : 0 ≤ ε ^ 4 * (1 + t ^ 6) := by positivity
  linarith

private lemma R_approx_pow4_le {t ε : ℝ} (hε_pos : 0 < ε) (hε_le1 : ε ≤ 1) :
    |R_approx t ε| ^ 4 ≤ 40000 * ε ^ 4 * (1 + t ^ 20) := by
  have hRa_bound : |R_approx t ε| ≤ 7 * (ε * (1 + |t| ^ 5)) := by
    unfold R_approx
    set S := ε * (1 + |t| ^ 5)
    have ht2 : |t| ^ 2 ≤ 1 + |t| ^ 5 := abs_pow_le_one_add (by omega)
    have ht3 : |t| ^ 3 ≤ 1 + |t| ^ 5 := abs_pow_le_one_add (by omega)
    have ht4 : |t| ^ 4 ≤ 1 + |t| ^ 5 := abs_pow_le_one_add (by omega)
    have ht5 : |t| ^ 5 ≤ 1 + |t| ^ 5 := by linarith
    have hε2_le : ε ^ 2 ≤ ε := by
      rw [sq]; exact mul_le_of_le_one_right (le_of_lt hε_pos) hε_le1
    have hε3_le : ε ^ 3 ≤ ε := by
      rw [show ε ^ 3 = ε ^ 2 * ε by ring]
      exact le_trans (mul_le_mul_of_nonneg_right hε2_le (le_of_lt hε_pos)) (by rw [← sq]; exact hε2_le)
    have htri : |-ε * t ^ 3 + ε ^ 2 * (-(3 / 2 : ℝ) * t ^ 4 + (3 / 2 : ℝ) * t ^ 2) +
          ε ^ 3 * (-(3 / 2 : ℝ) * t ^ 5 + t ^ 3)| ≤
        |-ε * t ^ 3| + |ε ^ 2 * (-(3 / 2 : ℝ) * t ^ 4)| + |ε ^ 2 * ((3 / 2 : ℝ) * t ^ 2)| +
        |ε ^ 3 * (-(3 / 2 : ℝ) * t ^ 5)| + |ε ^ 3 * t ^ 3| := by
      set A1 := -ε * t ^ 3
      set A2 := ε ^ 2 * (-(3 / 2 : ℝ) * t ^ 4)
      set A3 := ε ^ 2 * ((3 / 2 : ℝ) * t ^ 2)
      set A4 := ε ^ 3 * (-(3 / 2 : ℝ) * t ^ 5)
      set A5 := ε ^ 3 * t ^ 3
      have hrew : -ε * t ^ 3 + ε ^ 2 * (-(3 / 2 : ℝ) * t ^ 4 + (3 / 2 : ℝ) * t ^ 2) +
            ε ^ 3 * (-(3 / 2 : ℝ) * t ^ 5 + t ^ 3) = A1 + A2 + A3 + A4 + A5 := by
        dsimp only [A1, A2, A3, A4, A5]; ring
      rw [hrew]
      linarith [abs_add_le (A1 + A2 + A3 + A4) A5, abs_add_le (A1 + A2 + A3) A4,
                abs_add_le (A1 + A2) A3, abs_add_le A1 A2]
    have ha1 : |-ε * t ^ 3| ≤ S := by
      rw [abs_mul, abs_neg, abs_of_pos hε_pos, abs_pow]
      exact mul_le_mul_of_nonneg_left ht3 (le_of_lt hε_pos)
    have ha2 : |ε ^ 2 * (-(3 / 2 : ℝ) * t ^ 4)| ≤ (3 / 2 : ℝ) * S := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < ε ^ 2),
          abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), abs_pow]
      have hmul := mul_le_mul hε2_le ht4 (by positivity) (le_of_lt hε_pos)
      dsimp only [S]; linarith
    have ha3 : |ε ^ 2 * ((3 / 2 : ℝ) * t ^ 2)| ≤ (3 / 2 : ℝ) * S := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < ε ^ 2),
          abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), abs_pow]
      have hmul := mul_le_mul hε2_le ht2 (by positivity) (le_of_lt hε_pos)
      dsimp only [S]; linarith
    have ha4 : |ε ^ 3 * (-(3 / 2 : ℝ) * t ^ 5)| ≤ (3 / 2 : ℝ) * S := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < ε ^ 3),
          abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), abs_pow]
      have hmul := mul_le_mul hε3_le ht5 (by positivity) (le_of_lt hε_pos)
      dsimp only [S]; linarith
    have ha5 : |ε ^ 3 * t ^ 3| ≤ S := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < ε ^ 3), abs_pow]
      exact mul_le_mul hε3_le ht3 (by positivity) (le_of_lt hε_pos)
    have hS_nn : 0 ≤ S := by dsimp only [S]; positivity
    linarith
  have hpow4 : |R_approx t ε| ^ 4 ≤ (7 * (ε * (1 + |t| ^ 5))) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hRa_bound 4
  have h1t4 : (1 + |t| ^ 5) ^ 4 ≤ 16 * (1 + t ^ 20) := by
    have hsq : (1 + |t| ^ 5) ^ 2 ≤ 2 * (1 + |t| ^ 10) := by
      nlinarith [sq_nonneg (1 - |t| ^ 5), show (|t| ^ 5) ^ 2 = |t| ^ 10 by ring]
    have hsq2 : (1 + |t| ^ 10) ^ 2 ≤ 2 * (1 + |t| ^ 20) := by
      nlinarith [sq_nonneg (1 - |t| ^ 10), show (|t| ^ 10) ^ 2 = |t| ^ 20 by ring]
    have ht20 : |t| ^ 20 = t ^ 20 := by
      rw [show (20 : ℕ) = 2 * 10 by rfl, pow_mul, sq_abs, ← pow_mul]
    have hstep : (1 + |t| ^ 5) ^ 4 ≤ (2 * (1 + |t| ^ 10)) ^ 2 := by
      rw [show (1 + |t| ^ 5) ^ 4 = ((1 + |t| ^ 5) ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ (by positivity) hsq 2
    rw [ht20] at hsq2
    have hnn : 0 ≤ 1 + t ^ 20 := by positivity
    linarith [show (2 * (1 + |t| ^ 10)) ^ 2 = 4 * (1 + |t| ^ 10) ^ 2 by ring]
  calc |R_approx t ε| ^ 4 ≤ (7 * (ε * (1 + |t| ^ 5))) ^ 4 := hpow4
    _ = 2401 * ε ^ 4 * (1 + |t| ^ 5) ^ 4 := by ring
    _ ≤ 2401 * ε ^ 4 * (16 * (1 + t ^ 20)) := mul_le_mul_of_nonneg_left h1t4 (by positivity)
    _ ≤ 40000 * ε ^ 4 * (1 + t ^ 20) := by
        have : 0 ≤ ε ^ 4 * (1 + t ^ 20) := by positivity
        linarith

/-- Unified local exponential-ratio expansion to cubic order in `R_approx`. -/
lemma exp_ratio_approx {q m1 m2 : ℕ} {u : ℝ} (hq : 1 ≤ q) (hu : |u| ≤ 1 / 4)
    (hm1 : (m1 : ℝ) = (q : ℝ) * (1 + u)) (hm2 : (m2 : ℝ) = (q : ℝ) * (1 - 2 * u))
    (hR_small : |R_approx (u / (1 / Real.sqrt (q : ℝ))) (1 / Real.sqrt (q : ℝ))| ≤ 1 / 2)
    (herr_small : 300 * (1 / Real.sqrt (q : ℝ)) ^ 4 * (1 + (u / (1 / Real.sqrt (q : ℝ))) ^ 6) ≤ 1 / 2) :
    let ε := 1 / Real.sqrt (q : ℝ)
    let t := u / ε
    |((q.factorial : ℝ) ^ 3) / ((m1.factorial : ℝ) ^ 2 * (m2.factorial : ℝ)) -
        Real.exp (-3 * t ^ 2) * T3 (R_approx t ε)| ≤
      42000 * ε ^ 4 * (1 + t ^ 20) * Real.exp (-3 * t ^ 2) := by
  intro ε t
  change |R_approx t ε| ≤ 1 / 2 at hR_small
  change 300 * ε ^ 4 * (1 + t ^ 6) ≤ 1 / 2 at herr_small
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hsqq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
  have hε_pos : 0 < ε := by dsimp only [ε]; positivity
  have hε_le1 : ε ≤ 1 := by
    dsimp only [ε]
    rw [div_le_one hsqq]
    have : Real.sqrt 1 ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt hqR
    simpa using this
  have hrat_pos : 0 < ((q.factorial : ℝ) ^ 3) / ((m1.factorial : ℝ) ^ 2 * (m2.factorial : ℝ)) := by
    positivity
  set R := Real.log (((q.factorial : ℝ) ^ 3) / ((m1.factorial : ℝ) ^ 2 * (m2.factorial : ℝ))) - (-3 * t ^ 2)
  set Ra := R_approx t ε
  have hlog := log_ratio_approx hq hu hm1 hm2
  have hR_diff : |R - Ra| ≤ 300 * ε ^ 4 * (1 + t ^ 6) := by
    dsimp only [R, Ra]
    rw [show Real.log (((q.factorial : ℝ) ^ 3) / ((m1.factorial : ℝ) ^ 2 * (m2.factorial : ℝ))) - -3 * t ^ 2 -
        R_approx t ε =
        Real.log (((q.factorial : ℝ) ^ 3) / ((m1.factorial : ℝ) ^ 2 * (m2.factorial : ℝ))) -
          (-3 * t ^ 2 + R_approx t ε) by ring]
    exact hlog
  have hRa_le1 : |Ra| ≤ 1 := by linarith
  have hR_le1 : R ≤ 1 := by
    have h1 : |R| ≤ |Ra| + |R - Ra| := by
      have : R = Ra + (R - Ra) := by ring
      conv_lhs => rw [this]
      exact abs_add_le Ra (R - Ra)
    have h2 : |R| ≤ 1 := by linarith
    exact (abs_le.mp h2).2
  have hRa_ub : Ra ≤ 1 := (abs_le.mp hRa_le1).2
  have hrat_eq : ((q.factorial : ℝ) ^ 3) / ((m1.factorial : ℝ) ^ 2 * (m2.factorial : ℝ)) =
      Real.exp (-3 * t ^ 2) * Real.exp R := by
    rw [← Real.exp_add, show -3 * t ^ 2 + R =
      Real.log (((q.factorial : ℝ) ^ 3) / ((m1.factorial : ℝ) ^ 2 * (m2.factorial : ℝ))) by dsimp only [R]; ring]
    exact (Real.exp_log hrat_pos).symm
  rw [hrat_eq, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |Real.exp R - Real.exp Ra| ≤ 900 * ε ^ 4 * (1 + t ^ 6) := by
    have hl := abs_exp_sub_exp_le hR_le1 hRa_ub
    linarith
  have h2 : |Real.exp Ra - T3 Ra| ≤ |Ra| ^ 4 := by
    have hb := Real.exp_bound hRa_le1 (n := 4) (by norm_num)
    have hsum4 : ∑ m ∈ Finset.range 4, Ra ^ m / (m.factorial : ℝ) = T3 Ra := by
      unfold T3; simp [Finset.sum_range_succ, Nat.factorial]
    rw [hsum4] at hb
    have hcoef : (((Nat.succ 4 : ℕ) : ℝ) / ((Nat.factorial 4 : ℝ) * (4 : ℕ))) ≤ 1 := by
      norm_num [Nat.factorial]
    exact le_trans hb (mul_le_of_le_one_right (by positivity) hcoef)
  have hRa4 : |Ra| ^ 4 ≤ 40000 * ε ^ 4 * (1 + t ^ 20) := R_approx_pow4_le hε_pos hε_le1
  have ht6_le : 1 + t ^ 6 ≤ 2 * (1 + t ^ 20) := by
    have := abs_pow_le_one_add (x := t) (m := 6) (n := 20) (by omega)
    have h6 : |t| ^ 6 = t ^ 6 := by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, sq_abs, ← pow_mul]
    have h20 : |t| ^ 20 = t ^ 20 := by rw [show (20 : ℕ) = 2 * 10 by rfl, pow_mul, sq_abs, ← pow_mul]
    have ht20_nn : 0 ≤ t ^ 20 := by positivity
    rw [h6, h20] at this; linarith
  have hdiff_exp : |Real.exp R - T3 Ra| ≤ 42000 * ε ^ 4 * (1 + t ^ 20) := by
    have htri : |Real.exp R - T3 Ra| ≤ |Real.exp R - Real.exp Ra| + |Real.exp Ra - T3 Ra| := by
      have : Real.exp R - T3 Ra = (Real.exp R - Real.exp Ra) + (Real.exp Ra - T3 Ra) := by ring
      rw [this]; exact abs_add_le (Real.exp R - Real.exp Ra) (Real.exp Ra - T3 Ra)
    have h900 : 900 * ε ^ 4 * (1 + t ^ 6) ≤ 1800 * ε ^ 4 * (1 + t ^ 20) := by
      have := mul_le_mul_of_nonneg_left ht6_le (by positivity : 0 ≤ 900 * ε ^ 4)
      linarith
    have hnn : 0 ≤ ε ^ 4 * (1 + t ^ 20) := by positivity
    linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff_exp (le_of_lt (Real.exp_pos (-3 * t ^ 2)))
  linarith [show Real.exp (-3 * t ^ 2) * (42000 * ε ^ 4 * (1 + t ^ 20)) =
    42000 * ε ^ 4 * (1 + t ^ 20) * Real.exp (-3 * t ^ 2) by ring]

/-! ### Part 5: Exact polynomial decomposition of `T3(R_approx t ε) ∓ T3(R_approx (-t) ε)` -/

lemma T3_diff_bound {t ε : ℝ} (ht : 0 ≤ t) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |(T3 (R_approx t ε) - T3 (R_approx (-t) ε)) -
      (-2 * ε * t ^ 3 + ε ^ 3 * (-(1 / 3 : ℝ) * t ^ 9 + 3 * t ^ 7 - 6 * t ^ 5 + 2 * t ^ 3))| ≤
      100 * ε ^ 5 * (1 + t ^ 15) := by
  have hexact :
      (T3 (R_approx t ε) - T3 (R_approx (-t) ε)) -
        (-2 * ε * t ^ 3 + ε ^ 3 * (-(1 / 3 : ℝ) * t ^ 9 + 3 * t ^ 7 - 6 * t ^ 5 + 2 * t ^ 3)) =
      ε ^ 5 * ((-(15 / 4 : ℝ) * t ^ 11 + 10 * t ^ 9 - (39 / 4 : ℝ) * t ^ 7 + 3 * t ^ 5) +
        ε ^ 2 * (-(45 / 8 : ℝ) * t ^ 13 + 12 * t ^ 11 - (71 / 8 : ℝ) * t ^ 9 + (9 / 4 : ℝ) * t ^ 7) +
        ε ^ 4 * (-(9 / 8 : ℝ) * t ^ 15 + (9 / 4 : ℝ) * t ^ 13 - (3 / 2 : ℝ) * t ^ 11 + (1 / 3 : ℝ) * t ^ 9)) := by
    unfold T3 R_approx; ring
  rw [hexact, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ε ^ 5)]
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hε4 : ε ^ 4 ≤ 1 := by nlinarith
  have hpow : ∀ m ≤ 15, t ^ m ≤ 1 + t ^ 15 := fun m hm => by
    have := abs_pow_le_one_add (x := t) hm
    rwa [abs_of_nonneg ht] at this
  have h5 := hpow 5 (by omega)
  have h7 := hpow 7 (by omega)
  have h9 := hpow 9 (by omega)
  have h11 := hpow 11 (by omega)
  have h13 := hpow 13 (by omega)
  have h15 : t ^ 15 ≤ 1 + t ^ 15 := by linarith
  set Q1 := -(15 / 4 : ℝ) * t ^ 11 + 10 * t ^ 9 - (39 / 4 : ℝ) * t ^ 7 + 3 * t ^ 5
  set Q2 := -(45 / 8 : ℝ) * t ^ 13 + 12 * t ^ 11 - (71 / 8 : ℝ) * t ^ 9 + (9 / 4 : ℝ) * t ^ 7
  set Q3 := -(9 / 8 : ℝ) * t ^ 15 + (9 / 4 : ℝ) * t ^ 13 - (3 / 2 : ℝ) * t ^ 11 + (1 / 3 : ℝ) * t ^ 9
  have hp1 : |Q1| ≤ 30 * (1 + t ^ 15) := by
    dsimp only [Q1]; rw [abs_le]
    constructor <;> linarith [pow_nonneg ht 5, pow_nonneg ht 7, pow_nonneg ht 9, pow_nonneg ht 11]
  have hp2 : |Q2| ≤ 35 * (1 + t ^ 15) := by
    dsimp only [Q2]; rw [abs_le]
    constructor <;> linarith [pow_nonneg ht 7, pow_nonneg ht 9, pow_nonneg ht 11, pow_nonneg ht 13]
  have hp3 : |Q3| ≤ 10 * (1 + t ^ 15) := by
    dsimp only [Q3]; rw [abs_le]
    constructor <;> linarith [pow_nonneg ht 9, pow_nonneg ht 11, pow_nonneg ht 13, pow_nonneg ht 15]
  have htri : |Q1 + ε ^ 2 * Q2 + ε ^ 4 * Q3| ≤ |Q1| + |ε ^ 2 * Q2| + |ε ^ 4 * Q3| := by
    linarith [abs_add_le (Q1 + ε ^ 2 * Q2) (ε ^ 4 * Q3), abs_add_le Q1 (ε ^ 2 * Q2)]
  have h2 : |ε ^ 2 * Q2| ≤ 35 * (1 + t ^ 15) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact le_trans (mul_le_mul_of_nonneg_left hp2 (by positivity))
      (mul_le_of_le_one_left (by positivity) hε2)
  have h3 : |ε ^ 4 * Q3| ≤ 10 * (1 + t ^ 15) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact le_trans (mul_le_mul_of_nonneg_left hp3 (by positivity))
      (mul_le_of_le_one_left (by positivity) hε4)
  have hsum : |Q1 + ε ^ 2 * Q2 + ε ^ 4 * Q3| ≤ 100 * (1 + t ^ 15) := by
    linarith [show (0 : ℝ) ≤ 1 + t ^ 15 by positivity]
  have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ ε ^ 5)
  linarith [show ε ^ 5 * (100 * (1 + t ^ 15)) = 100 * ε ^ 5 * (1 + t ^ 15) by ring]

lemma T3_sum_bound {t ε : ℝ} (ht : 0 ≤ t) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |(T3 (R_approx t ε) + T3 (R_approx (-t) ε)) -
      (2 + ε ^ 2 * (t ^ 6 - 3 * t ^ 4 + 3 * t ^ 2))| ≤
      100 * ε ^ 4 * (1 + t ^ 14) := by
  have hexact :
      (T3 (R_approx t ε) + T3 (R_approx (-t) ε)) -
        (2 + ε ^ 2 * (t ^ 6 - 3 * t ^ 4 + 3 * t ^ 2)) =
      ε ^ 4 * ((-(3 / 2 : ℝ) * t ^ 10 + (27 / 4 : ℝ) * t ^ 8 - (13 / 2 : ℝ) * t ^ 6 + (9 / 4 : ℝ) * t ^ 4) +
        ε ^ 2 * (-(45 / 8 : ℝ) * t ^ 12 + (105 / 8 : ℝ) * t ^ 10 - (75 / 8 : ℝ) * t ^ 8 + (17 / 8 : ℝ) * t ^ 6) +
        ε ^ 4 * (-(27 / 8 : ℝ) * t ^ 14 + (63 / 8 : ℝ) * t ^ 12 - 6 * t ^ 10 + (3 / 2 : ℝ) * t ^ 8)) := by
    unfold T3 R_approx; ring
  rw [hexact, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ε ^ 4)]
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hε4 : ε ^ 4 ≤ 1 := by nlinarith
  have hpow : ∀ m ≤ 14, t ^ m ≤ 1 + t ^ 14 := fun m hm => by
    have := abs_pow_le_one_add (x := t) hm
    rwa [abs_of_nonneg ht] at this
  have h4 := hpow 4 (by omega)
  have h6 := hpow 6 (by omega)
  have h8 := hpow 8 (by omega)
  have h10 := hpow 10 (by omega)
  have h12 := hpow 12 (by omega)
  have h14 : t ^ 14 ≤ 1 + t ^ 14 := by linarith
  set Q1 := -(3 / 2 : ℝ) * t ^ 10 + (27 / 4 : ℝ) * t ^ 8 - (13 / 2 : ℝ) * t ^ 6 + (9 / 4 : ℝ) * t ^ 4
  set Q2 := -(45 / 8 : ℝ) * t ^ 12 + (105 / 8 : ℝ) * t ^ 10 - (75 / 8 : ℝ) * t ^ 8 + (17 / 8 : ℝ) * t ^ 6
  set Q3 := -(27 / 8 : ℝ) * t ^ 14 + (63 / 8 : ℝ) * t ^ 12 - 6 * t ^ 10 + (3 / 2 : ℝ) * t ^ 8
  have hp1 : |Q1| ≤ 20 * (1 + t ^ 14) := by
    dsimp only [Q1]; rw [abs_le]
    constructor <;> linarith [pow_nonneg ht 4, pow_nonneg ht 6, pow_nonneg ht 8, pow_nonneg ht 10]
  have hp2 : |Q2| ≤ 35 * (1 + t ^ 14) := by
    dsimp only [Q2]; rw [abs_le]
    constructor <;> linarith [pow_nonneg ht 6, pow_nonneg ht 8, pow_nonneg ht 10, pow_nonneg ht 12]
  have hp3 : |Q3| ≤ 25 * (1 + t ^ 14) := by
    dsimp only [Q3]; rw [abs_le]
    constructor <;> linarith [pow_nonneg ht 8, pow_nonneg ht 10, pow_nonneg ht 12, pow_nonneg ht 14]
  have htri : |Q1 + ε ^ 2 * Q2 + ε ^ 4 * Q3| ≤ |Q1| + |ε ^ 2 * Q2| + |ε ^ 4 * Q3| := by
    linarith [abs_add_le (Q1 + ε ^ 2 * Q2) (ε ^ 4 * Q3), abs_add_le Q1 (ε ^ 2 * Q2)]
  have h2 : |ε ^ 2 * Q2| ≤ 35 * (1 + t ^ 14) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact le_trans (mul_le_mul_of_nonneg_left hp2 (by positivity))
      (mul_le_of_le_one_left (by positivity) hε2)
  have h3 : |ε ^ 4 * Q3| ≤ 25 * (1 + t ^ 14) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact le_trans (mul_le_mul_of_nonneg_left hp3 (by positivity))
      (mul_le_of_le_one_left (by positivity) hε4)
  have hsum : |Q1 + ε ^ 2 * Q2 + ε ^ 4 * Q3| ≤ 100 * (1 + t ^ 14) := by
    linarith [show (0 : ℝ) ≤ 1 + t ^ 14 by positivity]
  have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ ε ^ 4)
  linarith [show ε ^ 4 * (100 * (1 + t ^ 14)) = 100 * ε ^ 4 * (1 + t ^ 14) by ring]

/-! ### Part 6: Helpers for summed Gaussian remainders and scaled Euler-Maclaurin limits -/

lemma sum_pow_exp_neg_three_sq_le (m : ℕ) {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) * h) ^ m * Real.exp (-3 * ((k : ℝ) * h) ^ 2) ≤
      (3 * Real.exp 1 * (1 + (m.factorial : ℝ))) / h := by
  calc ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) * h) ^ m * Real.exp (-3 * ((k : ℝ) * h) ^ 2)
      ≤ ∑ k ∈ Finset.Icc 1 K, Real.exp 1 * (1 + (m.factorial : ℝ)) * Real.exp (-((k : ℝ) * h)) := by
        refine Finset.sum_le_sum fun k _ => pow_mul_exp_neg_three_sq_le m (by positivity)
    _ = Real.exp 1 * (1 + (m.factorial : ℝ)) * ∑ k ∈ Finset.Icc 1 K, Real.exp (-(k : ℝ) * h) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by congr 2; ring
    _ ≤ Real.exp 1 * (1 + (m.factorial : ℝ)) * (3 / h) :=
        mul_le_mul_of_nonneg_left (sum_exp_neg_step_le hh0 hh1 K) (by positivity)
    _ = (3 * Real.exp 1 * (1 + (m.factorial : ℝ))) / h := by ring

/-- The discrete Gaussian moment sum `G_j(q) = (1/√q) * ∑_{k=1}^{K_cut q} (k/√q)^(2j+1) * exp(-3 k^2/q)`. -/
noncomputable def Gsum (j q : ℕ) : ℝ :=
  (1 / Real.sqrt (q : ℝ)) *
    ∑ k ∈ Finset.Icc 1 (K_cut q),
      ((k : ℝ) * (1 / Real.sqrt (q : ℝ))) ^ (2 * j + 1) *
        Real.exp (-3 * ((k : ℝ) * (1 / Real.sqrt (q : ℝ))) ^ 2)

lemma tendsto_inv_sqrt : Tendsto (fun q : ℕ => 1 / Real.sqrt (q : ℝ)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun q : ℕ => Real.sqrt (q : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => by
      refine ⟨Nat.ceil (max b 0 ^ 2), fun q hq => ?_⟩
      have h1 : max b 0 ^ 2 ≤ (q : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hq)
      have h2 := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_sq (le_max_right b 0)] at h2
      exact le_trans (le_max_left b 0) h2
  exact tendsto_const_nhds.div_atTop hsq

lemma tendsto_q_mul_Gsum_err (j : ℕ) :
    Tendsto (fun q : ℕ => (q : ℝ) *
      (Gsum j q - ((j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1)) -
        if j = 0 then 1 / (12 * (q : ℝ)) else 0))) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := oddGauss_sum_approx j
  set C_em : ℝ := (Nat.factorial 16 : ℝ) * 2 ^ 16
  have hlim : Tendsto (fun q : ℕ => C * (1 / Real.sqrt (q : ℝ) + 3 * C_em / (q : ℝ))) atTop (𝓝 0) := by
    have h1 := tendsto_inv_sqrt
    have h2 : Tendsto (fun q : ℕ => 3 * C_em / (q : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using (h1.add h2).const_mul C
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop (10 ^ 8)] with q hq
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 ≤ q := le_trans (by norm_num) hq
    exact_mod_cast this
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hsqq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
  have hε_pos : 0 < 1 / Real.sqrt (q : ℝ) := by positivity
  have hε_le1 : 1 / Real.sqrt (q : ℝ) ≤ 1 := by
    rw [div_le_one hsqq]
    have : Real.sqrt 1 ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt hqR
    simpa using this
  have hε2 : (1 / Real.sqrt (q : ℝ)) ^ 2 = 1 / (q : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hqpos)]
  have hmain := hC hε_pos (K_cut q)
  have hite : (if j = 0 then (1 / Real.sqrt (q : ℝ)) ^ 2 / 12 else 0) =
      (if j = 0 then 1 / (12 * (q : ℝ)) else 0) := by
    rw [hε2]; split_ifs <;> ring
  rw [hite] at hmain
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hqpos]
  have hcut := exp_cutoff_bound hq
  have h12 : 1 + 1 / Real.sqrt (q : ℝ) + (1 / Real.sqrt (q : ℝ)) ^ 2 ≤ 3 := by nlinarith
  have h3 : (1 / Real.sqrt (q : ℝ)) ^ 3 = 1 / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
    rw [show (1 / Real.sqrt (q : ℝ)) ^ 3 = (1 / Real.sqrt (q : ℝ)) ^ 2 * (1 / Real.sqrt (q : ℝ)) by ring, hε2]
    ring
  have hstep : (q : ℝ) * ((1 / Real.sqrt (q : ℝ)) ^ 3 +
      (1 + 1 / Real.sqrt (q : ℝ) + (1 / Real.sqrt (q : ℝ)) ^ 2) *
        Real.exp (-((K_cut q : ℝ) * (1 / Real.sqrt (q : ℝ))))) ≤
      1 / Real.sqrt (q : ℝ) + 3 * C_em / (q : ℝ) := by
    have ha : (q : ℝ) * (1 / Real.sqrt (q : ℝ)) ^ 3 = 1 / Real.sqrt (q : ℝ) := by
      rw [h3]; field_simp
    have hb : (q : ℝ) * ((1 + 1 / Real.sqrt (q : ℝ) + (1 / Real.sqrt (q : ℝ)) ^ 2) *
        Real.exp (-((K_cut q : ℝ) * (1 / Real.sqrt (q : ℝ))))) ≤ 3 * C_em / (q : ℝ) := by
      have hm1 := mul_le_mul h12 hcut (le_of_lt (Real.exp_pos _)) (by norm_num)
      have hm2 := mul_le_mul_of_nonneg_left hm1 (le_of_lt hqpos)
      have heq : (q : ℝ) * (3 * (C_em / (q : ℝ) ^ 2)) = 3 * C_em / (q : ℝ) := by field_simp
      linarith
    linarith
  calc (q : ℝ) * |Gsum j q - ((j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1)) -
          if j = 0 then 1 / (12 * (q : ℝ)) else 0)|
      ≤ (q : ℝ) * (C * ((1 / Real.sqrt (q : ℝ)) ^ 3 +
          (1 + 1 / Real.sqrt (q : ℝ) + (1 / Real.sqrt (q : ℝ)) ^ 2) *
            Real.exp (-((K_cut q : ℝ) * (1 / Real.sqrt (q : ℝ)))))) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt hqpos)
    _ = C * ((q : ℝ) * ((1 / Real.sqrt (q : ℝ)) ^ 3 +
          (1 + 1 / Real.sqrt (q : ℝ) + (1 / Real.sqrt (q : ℝ)) ^ 2) *
            Real.exp (-((K_cut q : ℝ) * (1 / Real.sqrt (q : ℝ)))))) := by ring
    _ ≤ C * (1 / Real.sqrt (q : ℝ) + 3 * C_em / (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep hC0

lemma tendsto_Gsum (j : ℕ) (hj : j ≠ 0) :
    Tendsto (fun q : ℕ => Gsum j q) atTop (𝓝 ((j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1)))) := by
  have hq := tendsto_q_mul_Gsum_err j
  simp only [hj, ↓reduceIte, sub_zero] at hq
  have hinv : Tendsto (fun q : ℕ => (q : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hprod : Tendsto (fun q : ℕ => (q : ℝ)⁻¹ * ((q : ℝ) * (Gsum j q - (j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1)))))
      atTop (𝓝 (0 * 0)) := hinv.mul hq
  rw [mul_zero] at hprod
  have hdiff : Tendsto (fun q : ℕ => Gsum j q - (j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1))) atTop (𝓝 0) := by
    refine hprod.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with q hq1
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    field_simp
  simpa using hdiff.add (tendsto_const_nhds (x := (j.factorial : ℝ) / (2 * (3 : ℝ) ^ (j + 1))))

/-! ### Part 7: Per-term local approximation on `1 ≤ k ≤ K_cut q` -/

private lemma local_smallness {q k : ℕ} (hq : 10 ^ 8 ≤ q) (hk : k ≤ K_cut q) (s : ℝ) (hs : |s| = 1) :
    let ε := 1 / Real.sqrt (q : ℝ)
    let u := s * (k : ℝ) / (q : ℝ)
    let t := u / ε
    |u| ≤ 1 / 4 ∧ |R_approx t ε| ≤ 1 / 2 ∧ 300 * ε ^ 4 * (1 + t ^ 6) ≤ 1 / 2 := by
  intro ε u t
  have hw10 := w8_ge_ten hq
  have hw_pos : 0 < w8 q := by linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by rw [← w8_pow8 q]; positivity
  have hsqq : Real.sqrt (q : ℝ) = (w8 q) ^ 4 := (w8_pow4 q).symm
  have hq8 : (q : ℝ) = (w8 q) ^ 8 := (w8_pow8 q).symm
  have hK_ub : (k : ℝ) ≤ (w8 q) ^ 5 := le_trans (by exact_mod_cast hk) (K_cut_bounds hq).2.1
  have hu_abs : |u| ≤ 1 / (w8 q) ^ 3 := by
    dsimp only [u]
    rw [abs_div, abs_mul, hs, one_mul, abs_of_nonneg (by positivity), abs_of_pos hqpos, hq8]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hmul := mul_le_mul_of_nonneg_right hK_ub (by positivity : 0 ≤ (w8 q) ^ 3)
    linarith [show (w8 q) ^ 5 * (w8 q) ^ 3 = 1 * (w8 q) ^ 8 by ring]
  have hw3 : (1000 : ℝ) ≤ (w8 q) ^ 3 := by
    have : (10 : ℝ) ^ 3 ≤ (w8 q) ^ 3 := pow_le_pow_left₀ (by norm_num) hw10 3
    norm_num at this; exact this
  have hu_le : |u| ≤ 1 / 4 := by
    refine le_trans hu_abs ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have ht_abs : |t| ≤ w8 q := by
    dsimp only [t, u, ε]
    rw [div_div_eq_mul_div, div_one, abs_mul, abs_div, abs_mul, hs, one_mul,
        abs_of_nonneg (by positivity), abs_of_pos hqpos,
        abs_of_pos (Real.sqrt_pos.mpr hqpos), hsqq, hq8]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hmul := mul_le_mul_of_nonneg_right hK_ub (by positivity : 0 ≤ (w8 q) ^ 4)
    linarith [show (w8 q) ^ 5 * (w8 q) ^ 4 = w8 q * (w8 q) ^ 8 by ring]
  have hε_eq : ε = 1 / (w8 q) ^ 4 := by dsimp only [ε]; rw [hsqq]
  have hε_pos : 0 < ε := by rw [hε_eq]; positivity
  have hRa_le : |R_approx t ε| ≤ 1 / 2 := by
    unfold R_approx
    have ht2 : |t| ^ 2 ≤ (w8 q) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ht_abs 2
    have ht3 : |t| ^ 3 ≤ (w8 q) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) ht_abs 3
    have ht4 : |t| ^ 4 ≤ (w8 q) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) ht_abs 4
    have ht5 : |t| ^ 5 ≤ (w8 q) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) ht_abs 5
    have htri : |-ε * t ^ 3 + ε ^ 2 * (-(3 / 2 : ℝ) * t ^ 4 + (3 / 2 : ℝ) * t ^ 2) +
          ε ^ 3 * (-(3 / 2 : ℝ) * t ^ 5 + t ^ 3)| ≤
        ε * |t| ^ 3 + (3 / 2 : ℝ) * ε ^ 2 * |t| ^ 4 + (3 / 2 : ℝ) * ε ^ 2 * |t| ^ 2 +
        (3 / 2 : ℝ) * ε ^ 3 * |t| ^ 5 + ε ^ 3 * |t| ^ 3 := by
      set A1 := -ε * t ^ 3
      set A2 := ε ^ 2 * (-(3 / 2 : ℝ) * t ^ 4)
      set A3 := ε ^ 2 * ((3 / 2 : ℝ) * t ^ 2)
      set A4 := ε ^ 3 * (-(3 / 2 : ℝ) * t ^ 5)
      set A5 := ε ^ 3 * t ^ 3
      have hrew : -ε * t ^ 3 + ε ^ 2 * (-(3 / 2 : ℝ) * t ^ 4 + (3 / 2 : ℝ) * t ^ 2) +
            ε ^ 3 * (-(3 / 2 : ℝ) * t ^ 5 + t ^ 3) = A1 + A2 + A3 + A4 + A5 := by
        dsimp only [A1, A2, A3, A4, A5]; ring
      rw [hrew]
      have hstep : |A1 + A2 + A3 + A4 + A5| ≤ |A1| + |A2| + |A3| + |A4| + |A5| := by
        linarith [abs_add_le (A1 + A2 + A3 + A4) A5, abs_add_le (A1 + A2 + A3) A4,
                  abs_add_le (A1 + A2) A3, abs_add_le A1 A2]
      have ha1 : |A1| = ε * |t| ^ 3 := by dsimp only [A1]; rw [abs_mul, abs_neg, abs_of_pos hε_pos, abs_pow]
      have ha2 : |A2| = (3 / 2 : ℝ) * ε ^ 2 * |t| ^ 4 := by
        dsimp only [A2]; rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < ε ^ 2),
            abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), abs_pow]; ring
      have ha3 : |A3| = (3 / 2 : ℝ) * ε ^ 2 * |t| ^ 2 := by
        dsimp only [A3]; rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < ε ^ 2),
            abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), abs_pow]; ring
      have ha4 : |A4| = (3 / 2 : ℝ) * ε ^ 3 * |t| ^ 5 := by
        dsimp only [A4]; rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < ε ^ 3),
            abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), abs_pow]; ring
      have ha5 : |A5| = ε ^ 3 * |t| ^ 3 := by
        dsimp only [A5]; rw [abs_mul, abs_of_pos (by positivity : 0 < ε ^ 3), abs_pow]
      linarith
    have hb1 : ε * |t| ^ 3 ≤ 1 / 10 := by
      rw [hε_eq, one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have h1 := mul_le_mul_of_nonneg_right ht3 (by norm_num : (0 : ℝ) ≤ 10)
      have h2 := mul_le_mul_of_nonneg_left hw10 (by positivity : 0 ≤ (w8 q) ^ 3)
      linarith [show (w8 q) ^ 3 * w8 q = 1 * (w8 q) ^ 4 by ring]
    have hb2' : ε ^ 2 * |t| ^ 4 ≤ 1 / 100 := by
      rw [hε_eq, one_div_pow, one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have hw4 : (100 : ℝ) ≤ (w8 q) ^ 4 := by
        have : (10 : ℝ) ^ 4 ≤ (w8 q) ^ 4 := pow_le_pow_left₀ (by norm_num) hw10 4
        norm_num at this; linarith
      have h1 := mul_le_mul_of_nonneg_right ht4 (by norm_num : (0 : ℝ) ≤ 100)
      have h2 := mul_le_mul_of_nonneg_left hw4 (by positivity : 0 ≤ (w8 q) ^ 4)
      linarith [show (w8 q) ^ 4 * (w8 q) ^ 4 = 1 * ((w8 q) ^ 4) ^ 2 by ring]
    have hb3' : ε ^ 2 * |t| ^ 2 ≤ 1 / 100 := by
      rw [hε_eq, one_div_pow, one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have hw6 : (100 : ℝ) ≤ (w8 q) ^ 6 := by
        have : (10 : ℝ) ^ 6 ≤ (w8 q) ^ 6 := pow_le_pow_left₀ (by norm_num) hw10 6
        norm_num at this; linarith
      have h1 := mul_le_mul_of_nonneg_right ht2 (by norm_num : (0 : ℝ) ≤ 100)
      have h2 := mul_le_mul_of_nonneg_left hw6 (by positivity : 0 ≤ (w8 q) ^ 2)
      linarith [show (w8 q) ^ 2 * (w8 q) ^ 6 = 1 * ((w8 q) ^ 4) ^ 2 by ring]
    have hb4' : ε ^ 3 * |t| ^ 5 ≤ 1 / 100 := by
      rw [hε_eq, one_div_pow, one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have hw7 : (100 : ℝ) ≤ (w8 q) ^ 7 := by
        have : (10 : ℝ) ^ 7 ≤ (w8 q) ^ 7 := pow_le_pow_left₀ (by norm_num) hw10 7
        norm_num at this; linarith
      have h1 := mul_le_mul_of_nonneg_right ht5 (by norm_num : (0 : ℝ) ≤ 100)
      have h2 := mul_le_mul_of_nonneg_left hw7 (by positivity : 0 ≤ (w8 q) ^ 5)
      linarith [show (w8 q) ^ 5 * (w8 q) ^ 7 = 1 * ((w8 q) ^ 4) ^ 3 by ring]
    have hb5' : ε ^ 3 * |t| ^ 3 ≤ 1 / 100 := by
      rw [hε_eq, one_div_pow, one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have hw9 : (100 : ℝ) ≤ (w8 q) ^ 9 := by
        have : (10 : ℝ) ^ 9 ≤ (w8 q) ^ 9 := pow_le_pow_left₀ (by norm_num) hw10 9
        norm_num at this; linarith
      have h1 := mul_le_mul_of_nonneg_right ht3 (by norm_num : (0 : ℝ) ≤ 100)
      have h2 := mul_le_mul_of_nonneg_left hw9 (by positivity : 0 ≤ (w8 q) ^ 3)
      linarith [show (w8 q) ^ 3 * (w8 q) ^ 9 = 1 * ((w8 q) ^ 4) ^ 3 by ring]
    linarith
  have herr_le : 300 * ε ^ 4 * (1 + t ^ 6) ≤ 1 / 2 := by
    have ht6 : t ^ 6 ≤ (w8 q) ^ 6 := by
      have h6 : |t| ^ 6 = t ^ 6 := by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, sq_abs, ← pow_mul]
      rw [← h6]
      exact pow_le_pow_left₀ (abs_nonneg _) ht_abs 6
    have h1t6 : 1 + t ^ 6 ≤ 2 * (w8 q) ^ 6 := by
      have hw6 : (1 : ℝ) ≤ (w8 q) ^ 6 := by
        have : (10 : ℝ) ^ 6 ≤ (w8 q) ^ 6 := pow_le_pow_left₀ (by norm_num) hw10 6
        norm_num at this; linarith
      linarith
    rw [hε_eq, one_div_pow]
    have hstep : 300 * (1 / ((w8 q) ^ 4) ^ 4) * (1 + t ^ 6) ≤ 600 / (w8 q) ^ 10 := by
      have hm := mul_le_mul_of_nonneg_left h1t6 (by positivity : 0 ≤ 300 * (1 / ((w8 q) ^ 4) ^ 4))
      have heq : 300 * (1 / ((w8 q) ^ 4) ^ 4) * (2 * (w8 q) ^ 6) = 600 / (w8 q) ^ 10 := by
        have hne : (w8 q) ^ 10 ≠ 0 := by positivity
        have hne6 : (w8 q) ^ 6 ≠ 0 := by positivity
        have h16 : ((w8 q) ^ 4) ^ 4 = (w8 q) ^ 10 * (w8 q) ^ 6 := by ring
        rw [h16]; field_simp; ring
      linarith
    have h600 : 600 / (w8 q) ^ 10 ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hw10_pow : (10 : ℝ) ^ 10 ≤ (w8 q) ^ 10 := pow_le_pow_left₀ (by norm_num) hw10 10
      norm_num at hw10_pow; linarith
    linarith
  exact ⟨hu_le, hRa_le, herr_le⟩

private lemma p3q_ratio_pos_eq {q k : ℕ} (h2k : 2 * k ≤ q) :
    p3q q (q + k) / p3q q q =
      ((q.factorial : ℝ) ^ 3) / (((q + k).factorial : ℝ) ^ 2 * ((q - 2 * k).factorial : ℝ)) := by
  rw [p3q_eq_of_le (by omega), p3q_eq_of_le (by omega)]
  have h1 : 3 * q - 2 * (q + k) = q - 2 * k := by omega
  have h2 : 3 * q - 2 * q = q := by omega
  rw [h1, h2]
  unfold T
  have hpref : ((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q) ≠ 0 := by positivity
  have hfq : (q.factorial : ℝ) ≠ 0 := by positivity
  have hfa : ((q + k).factorial : ℝ) ≠ 0 := by positivity
  have hfb : ((q - 2 * k).factorial : ℝ) ≠ 0 := by positivity
  field_simp

private lemma p3q_ratio_neg_eq {q k : ℕ} (hk : k ≤ q) :
    p3q q (q - k) / p3q q q =
      ((q.factorial : ℝ) ^ 3) / (((q - k).factorial : ℝ) ^ 2 * ((q + 2 * k).factorial : ℝ)) := by
  rw [p3q_eq_of_le (by omega), p3q_eq_of_le (by omega)]
  have h1 : 3 * q - 2 * (q - k) = q + 2 * k := by omega
  have h2 : 3 * q - 2 * q = q := by omega
  rw [h1, h2]
  unfold T
  have hpref : ((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q) ≠ 0 := by positivity
  have hfq : (q.factorial : ℝ) ≠ 0 := by positivity
  have hfa : ((q - k).factorial : ℝ) ≠ 0 := by positivity
  have hfb : ((q + 2 * k).factorial : ℝ) ≠ 0 := by positivity
  field_simp

private lemma local_diff_term_approx {q k : ℕ} (hq : 10 ^ 8 ≤ q) (hk : k ≤ K_cut q) :
    let ε := 1 / Real.sqrt (q : ℝ)
    let t := (k : ℝ) * ε
    |(p3q q (q + k) - p3q q (q - k)) / p3q q q -
      Real.exp (-3 * t ^ 2) *
        (-2 * ε * t ^ 3 + ε ^ 3 * (-(1 / 3 : ℝ) * t ^ 9 + 3 * t ^ 7 - 6 * t ^ 5 + 2 * t ^ 3))| ≤
      85000 * ε ^ 4 * (1 + t ^ 20) * Real.exp (-3 * t ^ 2) := by
  intro ε t
  have hK := K_cut_bounds hq
  have hq1 : 1 ≤ q := le_trans (by norm_num) hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hsqq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
  have hε_pos : 0 < ε := by dsimp only [ε]; positivity
  have hε_le1 : ε ≤ 1 := by
    dsimp only [ε]; rw [div_le_one hsqq]
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    simpa using Real.sqrt_le_sqrt this
  have ht_nn : 0 ≤ t := by dsimp only [t]; positivity
  have hpos_sm := local_smallness hq hk 1 (by norm_num)
  have hneg_sm := local_smallness hq hk (-1) (by norm_num)
  have ht_pos : (1 * (k : ℝ) / (q : ℝ)) / ε = t := by
    dsimp only [t, ε]
    rw [one_mul, div_div_eq_mul_div, div_one, mul_one_div]
    field_simp
    rw [Real.sq_sqrt (le_of_lt hqpos)]
  have ht_neg : (-1 * (k : ℝ) / (q : ℝ)) / ε = -t := by
    rw [show -1 * (k : ℝ) / (q : ℝ) = -(1 * (k : ℝ) / (q : ℝ)) by ring, neg_div, ht_pos]
  have hm1_pos : ((q + k : ℕ) : ℝ) = (q : ℝ) * (1 + 1 * (k : ℝ) / (q : ℝ)) := by
    push_cast; field_simp
  have hm2_pos : ((q - 2 * k : ℕ) : ℝ) = (q : ℝ) * (1 - 2 * (1 * (k : ℝ) / (q : ℝ))) := by
    rw [Nat.cast_sub (by omega)]; push_cast; field_simp
  have hm1_neg : ((q - k : ℕ) : ℝ) = (q : ℝ) * (1 + (-1) * (k : ℝ) / (q : ℝ)) := by
    rw [Nat.cast_sub (by omega)]; field_simp; ring
  have hm2_neg : ((q + 2 * k : ℕ) : ℝ) = (q : ℝ) * (1 - 2 * ((-1) * (k : ℝ) / (q : ℝ))) := by
    push_cast; field_simp; ring
  have happrox_pos := exp_ratio_approx hq1 hpos_sm.1 hm1_pos hm2_pos hpos_sm.2.1 hpos_sm.2.2
  have happrox_neg := exp_ratio_approx hq1 hneg_sm.1 hm1_neg hm2_neg hneg_sm.2.1 hneg_sm.2.2
  dsimp only at happrox_pos happrox_neg
  change |((q.factorial : ℝ) ^ 3) / (((q + k).factorial : ℝ) ^ 2 * ((q - 2 * k).factorial : ℝ)) -
      Real.exp (-3 * ((1 * (k : ℝ) / (q : ℝ)) / ε) ^ 2) * T3 (R_approx ((1 * (k : ℝ) / (q : ℝ)) / ε) ε)| ≤
      42000 * ε ^ 4 * (1 + ((1 * (k : ℝ) / (q : ℝ)) / ε) ^ 20) *
        Real.exp (-3 * ((1 * (k : ℝ) / (q : ℝ)) / ε) ^ 2) at happrox_pos
  change |((q.factorial : ℝ) ^ 3) / (((q - k).factorial : ℝ) ^ 2 * ((q + 2 * k).factorial : ℝ)) -
      Real.exp (-3 * ((-1 * (k : ℝ) / (q : ℝ)) / ε) ^ 2) * T3 (R_approx ((-1 * (k : ℝ) / (q : ℝ)) / ε) ε)| ≤
      42000 * ε ^ 4 * (1 + ((-1 * (k : ℝ) / (q : ℝ)) / ε) ^ 20) *
        Real.exp (-3 * ((-1 * (k : ℝ) / (q : ℝ)) / ε) ^ 2) at happrox_neg
  rw [ht_pos, ← p3q_ratio_pos_eq (by omega)] at happrox_pos
  rw [ht_neg, neg_sq, show (-t) ^ 20 = t ^ 20 by ring, ← p3q_ratio_neg_eq (by omega)] at happrox_neg
  have hT3 := T3_diff_bound ht_nn (le_of_lt hε_pos) hε_le1
  set D1 := p3q q (q + k) / p3q q q - Real.exp (-3 * t ^ 2) * T3 (R_approx t ε)
  set D2 := p3q q (q - k) / p3q q q - Real.exp (-3 * t ^ 2) * T3 (R_approx (-t) ε)
  set D3 := Real.exp (-3 * t ^ 2) *
      ((T3 (R_approx t ε) - T3 (R_approx (-t) ε)) -
        (-2 * ε * t ^ 3 + ε ^ 3 * (-(1 / 3 : ℝ) * t ^ 9 + 3 * t ^ 7 - 6 * t ^ 5 + 2 * t ^ 3)))
  have hsplit : (p3q q (q + k) - p3q q (q - k)) / p3q q q -
      Real.exp (-3 * t ^ 2) *
        (-2 * ε * t ^ 3 + ε ^ 3 * (-(1 / 3 : ℝ) * t ^ 9 + 3 * t ^ 7 - 6 * t ^ 5 + 2 * t ^ 3)) =
      D1 - D2 + D3 := by
    dsimp only [D1, D2, D3]; ring
  rw [hsplit]
  have htri : |D1 - D2 + D3| ≤ |D1| + |D2| + |D3| := by
    linarith [abs_add_le (D1 - D2) D3, abs_sub D1 D2]
  have hD3 : |D3| ≤ 200 * ε ^ 4 * (1 + t ^ 20) * Real.exp (-3 * t ^ 2) := by
    dsimp only [D3]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have ht15 : 1 + t ^ 15 ≤ 2 * (1 + t ^ 20) := by
      have := abs_pow_le_one_add (x := t) (m := 15) (n := 20) (by omega)
      have ht20_nn : 0 ≤ t ^ 20 := by positivity
      rw [abs_of_nonneg ht_nn] at this; linarith
    have hε5 : ε ^ 5 ≤ ε ^ 4 := by
      rw [show ε ^ 5 = ε ^ 4 * ε by ring]; exact mul_le_of_le_one_right (by positivity) hε_le1
    have hm1 := mul_le_mul_of_nonneg_left hT3 (le_of_lt (Real.exp_pos (-3 * t ^ 2)))
    have hm2 : 100 * ε ^ 5 * (1 + t ^ 15) ≤ 200 * ε ^ 4 * (1 + t ^ 20) := by
      have := mul_le_mul hε5 ht15 (by positivity) (by positivity)
      linarith
    have hm3 := mul_le_mul_of_nonneg_left hm2 (le_of_lt (Real.exp_pos (-3 * t ^ 2)))
    linarith
  have hnn : 0 ≤ ε ^ 4 * (1 + t ^ 20) * Real.exp (-3 * t ^ 2) := by positivity
  linarith

private lemma local_sum_term_approx {q k : ℕ} (hq : 10 ^ 8 ≤ q) (hk : k ≤ K_cut q) :
    let ε := 1 / Real.sqrt (q : ℝ)
    let t := (k : ℝ) * ε
    |(p3q q (q + k) + p3q q (q - k)) / p3q q q -
      Real.exp (-3 * t ^ 2) * (2 + ε ^ 2 * (t ^ 6 - 3 * t ^ 4 + 3 * t ^ 2))| ≤
      85000 * ε ^ 4 * (1 + t ^ 20) * Real.exp (-3 * t ^ 2) := by
  intro ε t
  have hK := K_cut_bounds hq
  have hq1 : 1 ≤ q := le_trans (by norm_num) hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hsqq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
  have hε_pos : 0 < ε := by dsimp only [ε]; positivity
  have hε_le1 : ε ≤ 1 := by
    dsimp only [ε]; rw [div_le_one hsqq]
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    simpa using Real.sqrt_le_sqrt this
  have ht_nn : 0 ≤ t := by dsimp only [t]; positivity
  have hpos_sm := local_smallness hq hk 1 (by norm_num)
  have hneg_sm := local_smallness hq hk (-1) (by norm_num)
  have ht_pos : (1 * (k : ℝ) / (q : ℝ)) / ε = t := by
    dsimp only [t, ε]
    rw [one_mul, div_div_eq_mul_div, div_one, mul_one_div]
    field_simp
    rw [Real.sq_sqrt (le_of_lt hqpos)]
  have ht_neg : (-1 * (k : ℝ) / (q : ℝ)) / ε = -t := by
    rw [show -1 * (k : ℝ) / (q : ℝ) = -(1 * (k : ℝ) / (q : ℝ)) by ring, neg_div, ht_pos]
  have hm1_pos : ((q + k : ℕ) : ℝ) = (q : ℝ) * (1 + 1 * (k : ℝ) / (q : ℝ)) := by
    push_cast; field_simp
  have hm2_pos : ((q - 2 * k : ℕ) : ℝ) = (q : ℝ) * (1 - 2 * (1 * (k : ℝ) / (q : ℝ))) := by
    rw [Nat.cast_sub (by omega)]; push_cast; field_simp
  have hm1_neg : ((q - k : ℕ) : ℝ) = (q : ℝ) * (1 + (-1) * (k : ℝ) / (q : ℝ)) := by
    rw [Nat.cast_sub (by omega)]; field_simp; ring
  have hm2_neg : ((q + 2 * k : ℕ) : ℝ) = (q : ℝ) * (1 - 2 * ((-1) * (k : ℝ) / (q : ℝ))) := by
    push_cast; field_simp; ring
  have happrox_pos := exp_ratio_approx hq1 hpos_sm.1 hm1_pos hm2_pos hpos_sm.2.1 hpos_sm.2.2
  have happrox_neg := exp_ratio_approx hq1 hneg_sm.1 hm1_neg hm2_neg hneg_sm.2.1 hneg_sm.2.2
  dsimp only at happrox_pos happrox_neg
  change |((q.factorial : ℝ) ^ 3) / (((q + k).factorial : ℝ) ^ 2 * ((q - 2 * k).factorial : ℝ)) -
      Real.exp (-3 * ((1 * (k : ℝ) / (q : ℝ)) / ε) ^ 2) * T3 (R_approx ((1 * (k : ℝ) / (q : ℝ)) / ε) ε)| ≤
      42000 * ε ^ 4 * (1 + ((1 * (k : ℝ) / (q : ℝ)) / ε) ^ 20) *
        Real.exp (-3 * ((1 * (k : ℝ) / (q : ℝ)) / ε) ^ 2) at happrox_pos
  change |((q.factorial : ℝ) ^ 3) / (((q - k).factorial : ℝ) ^ 2 * ((q + 2 * k).factorial : ℝ)) -
      Real.exp (-3 * ((-1 * (k : ℝ) / (q : ℝ)) / ε) ^ 2) * T3 (R_approx ((-1 * (k : ℝ) / (q : ℝ)) / ε) ε)| ≤
      42000 * ε ^ 4 * (1 + ((-1 * (k : ℝ) / (q : ℝ)) / ε) ^ 20) *
        Real.exp (-3 * ((-1 * (k : ℝ) / (q : ℝ)) / ε) ^ 2) at happrox_neg
  rw [ht_pos, ← p3q_ratio_pos_eq (by omega)] at happrox_pos
  rw [ht_neg, neg_sq, show (-t) ^ 20 = t ^ 20 by ring, ← p3q_ratio_neg_eq (by omega)] at happrox_neg
  have hT3 := T3_sum_bound ht_nn (le_of_lt hε_pos) hε_le1
  set D1 := p3q q (q + k) / p3q q q - Real.exp (-3 * t ^ 2) * T3 (R_approx t ε)
  set D2 := p3q q (q - k) / p3q q q - Real.exp (-3 * t ^ 2) * T3 (R_approx (-t) ε)
  set D3 := Real.exp (-3 * t ^ 2) *
      ((T3 (R_approx t ε) + T3 (R_approx (-t) ε)) -
        (2 + ε ^ 2 * (t ^ 6 - 3 * t ^ 4 + 3 * t ^ 2)))
  have hsplit : (p3q q (q + k) + p3q q (q - k)) / p3q q q -
      Real.exp (-3 * t ^ 2) * (2 + ε ^ 2 * (t ^ 6 - 3 * t ^ 4 + 3 * t ^ 2)) =
      D1 + D2 + D3 := by
    dsimp only [D1, D2, D3]; ring
  rw [hsplit]
  have htri : |D1 + D2 + D3| ≤ |D1| + |D2| + |D3| := by
    linarith [abs_add_le (D1 + D2) D3, abs_add_le D1 D2]
  have hD3 : |D3| ≤ 200 * ε ^ 4 * (1 + t ^ 20) * Real.exp (-3 * t ^ 2) := by
    dsimp only [D3]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have ht14 : 1 + t ^ 14 ≤ 2 * (1 + t ^ 20) := by
      have := abs_pow_le_one_add (x := t) (m := 14) (n := 20) (by omega)
      have ht20_nn : 0 ≤ t ^ 20 := by positivity
      rw [abs_of_nonneg ht_nn] at this; linarith
    have hm1 := mul_le_mul_of_nonneg_left hT3 (le_of_lt (Real.exp_pos (-3 * t ^ 2)))
    have hm2 : 100 * ε ^ 4 * (1 + t ^ 14) ≤ 200 * ε ^ 4 * (1 + t ^ 20) := by
      have := mul_le_mul_of_nonneg_left ht14 (by positivity : 0 ≤ 100 * ε ^ 4)
      linarith
    have hm3 := mul_le_mul_of_nonneg_left hm2 (le_of_lt (Real.exp_pos (-3 * t ^ 2)))
    linarith
  have hnn : 0 ≤ ε ^ 4 * (1 + t ^ 20) * Real.exp (-3 * t ^ 2) := by positivity
  linarith

/-! ### Part 8: Main asymptotic limit theorems for `sumA`, `sumB`, `sumC` -/

private lemma sum_Icc_split {K q : ℕ} (hKq : K ≤ q) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 q, f k =
      (∑ k ∈ Finset.Icc 1 K, f k) + (∑ k ∈ Finset.Icc (K + 1) q, f k) := by
  have hunion : Finset.Icc 1 q = Finset.Icc 1 K ∪ Finset.Icc (K + 1) q := by
    ext k; simp only [mem_Icc, mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 K) (Finset.Icc (K + 1) q) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2; simp only [mem_Icc] at hk1 hk2; omega
  rw [hunion, Finset.sum_union hdisj]

private lemma abs_p3q_tail_sum_le {q : ℕ} (hq : 10 ^ 8 ≤ q) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Finset.Icc (K_cut q + 1) q, |w k| ≤ 1) (sgn : ℝ) (hsgn : |sgn| = 1) :
    |∑ k ∈ Finset.Icc (K_cut q + 1) q, w k * ((p3q q (q + k) + sgn * p3q q (q - k)) / p3q q q)| ≤
      2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
  have hq1 : 1 ≤ q := le_trans (by norm_num) hq
  have hp0 : 0 < p3q q q := p3q_center_pos q
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  set M := ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) ^ 2 * Real.sqrt (q : ℝ))
  have hterm : ∀ k ∈ Finset.Icc (K_cut q + 1) q,
      |w k * ((p3q q (q + k) + sgn * p3q q (q - k)) / p3q q q)| ≤ 2 * M := by
    intro k hk
    rw [mem_Icc] at hk
    have hgt : K_cut q < k := by omega
    have hr := le_trans (p3q_right_ratio_le q k hq1) (exp_tail_bound hq hgt)
    have hl := le_trans (p3q_left_ratio_le q k hq1 hk.2) (exp_tail_bound hq hgt)
    have hr_nn : 0 ≤ p3q q (q + k) / p3q q q := by
      refine div_nonneg ?_ (le_of_lt hp0)
      unfold p3q; split_ifs
      · have := T_pos (q + k) (q + k) (3 * q - 2 * (q + k)); positivity
      · rfl
    have hl_nn : 0 ≤ p3q q (q - k) / p3q q q := by
      refine div_nonneg ?_ (le_of_lt hp0)
      rw [p3q_eq_of_le (by omega)]
      have := T_pos (q - k) (q - k) (3 * q - 2 * (q - k)); positivity
    have hsum_abs : |(p3q q (q + k) + sgn * p3q q (q - k)) / p3q q q| ≤ 2 * M := by
      rw [add_div, mul_div_assoc]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, hsgn, one_mul, abs_of_nonneg hr_nn, abs_of_nonneg hl_nn]
      dsimp only [M]; linarith
    rw [abs_mul]
    have hwk := hw k (mem_Icc.mpr hk)
    exact le_trans (mul_le_mul hwk hsum_abs (abs_nonneg _) (by norm_num)) (by linarith)
  have hcard : ((Finset.Icc (K_cut q + 1) q).card : ℝ) ≤ (q : ℝ) := by
    have : (Finset.Icc (K_cut q + 1) q).card ≤ q := by simp only [Nat.card_Icc]; omega
    exact_mod_cast this
  calc |∑ k ∈ Finset.Icc (K_cut q + 1) q, w k * ((p3q q (q + k) + sgn * p3q q (q - k)) / p3q q q)|
      ≤ ∑ k ∈ Finset.Icc (K_cut q + 1) q, |w k * ((p3q q (q + k) + sgn * p3q q (q - k)) / p3q q q)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Icc (K_cut q + 1) q, (2 * M) := Finset.sum_le_sum hterm
    _ = ((Finset.Icc (K_cut q + 1) q).card : ℝ) * (2 * M) := by simp
    _ ≤ (q : ℝ) * (2 * M) := mul_le_mul_of_nonneg_right hcard (by dsimp only [M]; positivity)
    _ = 2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
        dsimp only [M]; field_simp

/-- Asymptotic expansion of `A(q)`: `q * (sumA q - (-1/9 - 4/(243 q))) → 0`. -/
theorem tendsto_sumA :
    Tendsto (fun q : ℕ => (q : ℝ) * (sumA q - (-(1 / 9 : ℝ) - 4 / (243 * (q : ℝ))))) atTop (𝓝 0) := by
  let mainA : ℕ → ℝ := fun q =>
    -2 * Gsum 1 q + (1 / (q : ℝ)) * (-(1 / 3 : ℝ) * Gsum 4 q + 3 * Gsum 3 q - 6 * Gsum 2 q + 2 * Gsum 1 q)
  have hmain_lim : Tendsto (fun q : ℕ => (q : ℝ) * (mainA q - (-(1 / 9 : ℝ) - 4 / (243 * (q : ℝ))))) atTop (𝓝 0) := by
    have h1 := tendsto_q_mul_Gsum_err 1
    norm_num [Nat.factorial] at h1
    have hG1 := tendsto_Gsum 1 (by norm_num)
    have hG2 := tendsto_Gsum 2 (by norm_num)
    have hG3 := tendsto_Gsum 3 (by norm_num)
    have hG4 := tendsto_Gsum 4 (by norm_num)
    have hcomb : Tendsto (fun q : ℕ =>
        -2 * ((q : ℝ) * (Gsum 1 q - (1 : ℝ) / 18)) +
        (-(1 / 3 : ℝ) * Gsum 4 q + 3 * Gsum 3 q - 6 * Gsum 2 q + 2 * Gsum 1 q + (4 / 243 : ℝ))) atTop (𝓝 0) := by
      have h0 : -2 * (0 : ℝ) +
          (-(1 / 3 : ℝ) * ((Nat.factorial 4 : ℝ) / (2 * (3 : ℝ) ^ (4 + 1))) +
           3 * ((Nat.factorial 3 : ℝ) / (2 * (3 : ℝ) ^ (3 + 1))) -
           6 * ((Nat.factorial 2 : ℝ) / (2 * (3 : ℝ) ^ (2 + 1))) +
           2 * ((Nat.factorial 1 : ℝ) / (2 * (3 : ℝ) ^ (1 + 1))) + (4 / 243 : ℝ)) = 0 := by
        norm_num [Nat.factorial]
      rw [← h0]
      exact (h1.const_mul (-2)).add
        (((((hG4.const_mul (-(1 / 3 : ℝ))).add (hG3.const_mul 3)).sub (hG2.const_mul 6)).add
          (hG1.const_mul 2)).add (tendsto_const_nhds (x := (4 / 243 : ℝ))))
    refine hcomb.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with q hq
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    dsimp only [mainA]
    field_simp; ring
  set C_rem : ℝ := 85000 * (3 * Real.exp 1 * (1 + (Nat.factorial 0 : ℝ)) +
      3 * Real.exp 1 * (1 + (Nat.factorial 20 : ℝ))) + 2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10)
  have hrem_lim : Tendsto (fun q : ℕ => (q : ℝ) * (sumA q - mainA q)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using tendsto_inv_sqrt.const_mul C_rem)
    filter_upwards [Filter.eventually_ge_atTop (10 ^ 8)] with q hq
    have hK := K_cut_bounds hq
    have hq1 : 1 ≤ q := le_trans (by norm_num) hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
    have hsqq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
    set ε := 1 / Real.sqrt (q : ℝ)
    have hε_pos : 0 < ε := by dsimp only [ε]; positivity
    have hε_le1 : ε ≤ 1 := by
      dsimp only [ε]; rw [div_le_one hsqq]
      have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      simpa using Real.sqrt_le_sqrt this
    have hε2 : ε ^ 2 = 1 / (q : ℝ) := by
      dsimp only [ε]; rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hqpos)]
    have hmain_eq : mainA q = ∑ k ∈ Finset.Icc 1 (K_cut q),
        Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
          (-2 * ε * ((k : ℝ) * ε) ^ 3 +
            ε ^ 3 * (-(1 / 3 : ℝ) * ((k : ℝ) * ε) ^ 9 + 3 * ((k : ℝ) * ε) ^ 7 -
              6 * ((k : ℝ) * ε) ^ 5 + 2 * ((k : ℝ) * ε) ^ 3)) := by
      dsimp only [mainA]; unfold Gsum
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hε2]
      dsimp only [ε]
      ring
    have hsumA_split : sumA q =
        (∑ k ∈ Finset.Icc 1 (K_cut q), (p3q q (q + k) - p3q q (q - k)) / p3q q q) +
        (∑ k ∈ Finset.Icc (K_cut q + 1) q, (p3q q (q + k) - p3q q (q - k)) / p3q q q) := by
      unfold sumA
      rw [Finset.sum_div, sum_Icc_split (K := K_cut q) (by omega)]
    rw [hsumA_split, hmain_eq, Real.norm_eq_abs, abs_mul, abs_of_pos hqpos]
    have hdiff_split :
        ((∑ k ∈ Finset.Icc 1 (K_cut q), (p3q q (q + k) - p3q q (q - k)) / p3q q q) +
          (∑ k ∈ Finset.Icc (K_cut q + 1) q, (p3q q (q + k) - p3q q (q - k)) / p3q q q)) -
        (∑ k ∈ Finset.Icc 1 (K_cut q),
          Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
            (-2 * ε * ((k : ℝ) * ε) ^ 3 +
              ε ^ 3 * (-(1 / 3 : ℝ) * ((k : ℝ) * ε) ^ 9 + 3 * ((k : ℝ) * ε) ^ 7 -
                6 * ((k : ℝ) * ε) ^ 5 + 2 * ((k : ℝ) * ε) ^ 3))) =
        (∑ k ∈ Finset.Icc 1 (K_cut q),
          ((p3q q (q + k) - p3q q (q - k)) / p3q q q -
            Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
              (-2 * ε * ((k : ℝ) * ε) ^ 3 +
                ε ^ 3 * (-(1 / 3 : ℝ) * ((k : ℝ) * ε) ^ 9 + 3 * ((k : ℝ) * ε) ^ 7 -
                  6 * ((k : ℝ) * ε) ^ 5 + 2 * ((k : ℝ) * ε) ^ 3)))) +
        (∑ k ∈ Finset.Icc (K_cut q + 1) q, (p3q q (q + k) - p3q q (q - k)) / p3q q q) := by
      rw [Finset.sum_sub_distrib]; ring
    rw [hdiff_split]
    have hbody : |∑ k ∈ Finset.Icc 1 (K_cut q),
        ((p3q q (q + k) - p3q q (q - k)) / p3q q q -
          Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
            (-2 * ε * ((k : ℝ) * ε) ^ 3 +
              ε ^ 3 * (-(1 / 3 : ℝ) * ((k : ℝ) * ε) ^ 9 + 3 * ((k : ℝ) * ε) ^ 7 -
                6 * ((k : ℝ) * ε) ^ 5 + 2 * ((k : ℝ) * ε) ^ 3)))| ≤
        85000 * (3 * Real.exp 1 * (1 + (Nat.factorial 0 : ℝ)) +
          3 * Real.exp 1 * (1 + (Nat.factorial 20 : ℝ))) * ε ^ 3 := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have h1 : ∑ k ∈ Finset.Icc 1 (K_cut q),
          |(p3q q (q + k) - p3q q (q - k)) / p3q q q -
            Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
              (-2 * ε * ((k : ℝ) * ε) ^ 3 +
                ε ^ 3 * (-(1 / 3 : ℝ) * ((k : ℝ) * ε) ^ 9 + 3 * ((k : ℝ) * ε) ^ 7 -
                  6 * ((k : ℝ) * ε) ^ 5 + 2 * ((k : ℝ) * ε) ^ 3))| ≤
          ∑ k ∈ Finset.Icc 1 (K_cut q),
            85000 * ε ^ 4 * (1 + ((k : ℝ) * ε) ^ 20) * Real.exp (-3 * ((k : ℝ) * ε) ^ 2) :=
        Finset.sum_le_sum fun k hk => local_diff_term_approx hq (mem_Icc.mp hk).2
      have h2 : ∑ k ∈ Finset.Icc 1 (K_cut q),
            85000 * ε ^ 4 * (1 + ((k : ℝ) * ε) ^ 20) * Real.exp (-3 * ((k : ℝ) * ε) ^ 2) =
          85000 * ε ^ 4 * ((∑ k ∈ Finset.Icc 1 (K_cut q), ((k : ℝ) * ε) ^ 0 * Real.exp (-3 * ((k : ℝ) * ε) ^ 2)) +
            (∑ k ∈ Finset.Icc 1 (K_cut q), ((k : ℝ) * ε) ^ 20 * Real.exp (-3 * ((k : ℝ) * ε) ^ 2))) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by simp [pow_zero]; ring
      have h3 := sum_pow_exp_neg_three_sq_le 0 hε_pos hε_le1 (K_cut q)
      have h4 := sum_pow_exp_neg_three_sq_le 20 hε_pos hε_le1 (K_cut q)
      rw [h2] at h1
      have h5 := mul_le_mul_of_nonneg_left (add_le_add h3 h4) (by positivity : 0 ≤ 85000 * ε ^ 4)
      have h6 : 85000 * ε ^ 4 *
          ((3 * Real.exp 1 * (1 + (Nat.factorial 0 : ℝ))) / ε +
           (3 * Real.exp 1 * (1 + (Nat.factorial 20 : ℝ))) / ε) =
          85000 * (3 * Real.exp 1 * (1 + (Nat.factorial 0 : ℝ)) +
            3 * Real.exp 1 * (1 + (Nat.factorial 20 : ℝ))) * ε ^ 3 := by
        field_simp
      linarith
    have htail : |∑ k ∈ Finset.Icc (K_cut q + 1) q, (p3q q (q + k) - p3q q (q - k)) / p3q q q| ≤
        2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
      have h := abs_p3q_tail_sum_le hq (fun _ => 1) (fun _ _ => by norm_num) (-1) (by norm_num)
      refine le_trans (le_of_eq ?_) h
      congr 1; refine Finset.sum_congr rfl fun k _ => by ring
    have hqε3 : (q : ℝ) * ε ^ 3 = ε := by
      rw [show ε ^ 3 = ε ^ 2 * ε by ring, hε2]; field_simp
    have hqtail : (q : ℝ) * (2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) * Real.sqrt (q : ℝ))) =
        2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) * ε := by
      dsimp only [ε]; field_simp
    have htri := abs_add_le
      (∑ k ∈ Finset.Icc 1 (K_cut q),
        ((p3q q (q + k) - p3q q (q - k)) / p3q q q -
          Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
            (-2 * ε * ((k : ℝ) * ε) ^ 3 +
              ε ^ 3 * (-(1 / 3 : ℝ) * ((k : ℝ) * ε) ^ 9 + 3 * ((k : ℝ) * ε) ^ 7 -
                6 * ((k : ℝ) * ε) ^ 5 + 2 * ((k : ℝ) * ε) ^ 3))))
      (∑ k ∈ Finset.Icc (K_cut q + 1) q, (p3q q (q + k) - p3q q (q - k)) / p3q q q)
    have hmul := mul_le_mul_of_nonneg_left (le_trans htri (add_le_add hbody htail)) (le_of_lt hqpos)
    dsimp only [C_rem]
    calc (q : ℝ) * |_| ≤ (q : ℝ) * (85000 * (3 * Real.exp 1 * (1 + (Nat.factorial 0 : ℝ)) +
            3 * Real.exp 1 * (1 + (Nat.factorial 20 : ℝ))) * ε ^ 3 +
            2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) * Real.sqrt (q : ℝ))) := hmul
      _ = (85000 * (3 * Real.exp 1 * (1 + (Nat.factorial 0 : ℝ)) +
            3 * Real.exp 1 * (1 + (Nat.factorial 20 : ℝ))) +
            2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10)) * ε := by
          rw [mul_add, ← mul_assoc, mul_comm (q : ℝ), mul_assoc, hqε3, hqtail]; ring
      _ = (85000 * (3 * Real.exp 1 * (1 + (Nat.factorial 0 : ℝ)) +
            3 * Real.exp 1 * (1 + (Nat.factorial 20 : ℝ))) +
            2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10)) * (Real.sqrt (q : ℝ))⁻¹ := by
          dsimp only [ε]; rw [one_div]
  have hcomb := hrem_lim.add hmain_lim
  rw [add_zero] at hcomb
  refine hcomb.congr fun q => by ring

/-- Asymptotic expansion of `B(q)`: `q * (sumB q - (1/3 - 2/(27 q))) → 0`. -/
theorem tendsto_sumB :
    Tendsto (fun q : ℕ => (q : ℝ) * (sumB q - (1 / 3 - 2 / (27 * (q : ℝ))))) atTop (𝓝 0) := by
  let mainB : ℕ → ℝ := fun q =>
    2 * Gsum 0 q + (1 / (q : ℝ)) * (Gsum 3 q - 3 * Gsum 2 q + 3 * Gsum 1 q)
  have hmain_lim : Tendsto (fun q : ℕ => (q : ℝ) * (mainB q - (1 / 3 - 2 / (27 * (q : ℝ))))) atTop (𝓝 0) := by
    have h0 := tendsto_q_mul_Gsum_err 0
    norm_num [Nat.factorial] at h0
    have hG1 := tendsto_Gsum 1 (by norm_num)
    have hG2 := tendsto_Gsum 2 (by norm_num)
    have hG3 := tendsto_Gsum 3 (by norm_num)
    have hcomb : Tendsto (fun q : ℕ =>
        2 * ((q : ℝ) * (Gsum 0 q - ((1 : ℝ) / 6 - (q : ℝ)⁻¹ * (1 / 12)))) +
        (Gsum 3 q - 3 * Gsum 2 q + 3 * Gsum 1 q - (5 / 54 : ℝ))) atTop (𝓝 0) := by
      have hzero : 2 * (0 : ℝ) +
          (((Nat.factorial 3 : ℝ) / (2 * (3 : ℝ) ^ (3 + 1))) -
           3 * ((Nat.factorial 2 : ℝ) / (2 * (3 : ℝ) ^ (2 + 1))) +
           3 * ((Nat.factorial 1 : ℝ) / (2 * (3 : ℝ) ^ (1 + 1))) - (5 / 54 : ℝ)) = 0 := by
        norm_num [Nat.factorial]
      rw [← hzero]
      exact (h0.const_mul 2).add
        (((hG3.sub (hG2.const_mul 3)).add (hG1.const_mul 3)).sub (tendsto_const_nhds (x := (5 / 54 : ℝ))))
    refine hcomb.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with q hq
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    dsimp only [mainB]
    field_simp; ring
  set C_rem : ℝ := 85000 * (3 * Real.exp 1 * (1 + (Nat.factorial 1 : ℝ)) +
      3 * Real.exp 1 * (1 + (Nat.factorial 21 : ℝ))) + 2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10)
  have hrem_lim : Tendsto (fun q : ℕ => (q : ℝ) * (sumB q - mainB q)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using tendsto_inv_sqrt.const_mul C_rem)
    filter_upwards [Filter.eventually_ge_atTop (10 ^ 8)] with q hq
    have hK := K_cut_bounds hq
    have hq1 : 1 ≤ q := le_trans (by norm_num) hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
    have hsqq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
    set ε := 1 / Real.sqrt (q : ℝ)
    have hε_pos : 0 < ε := by dsimp only [ε]; positivity
    have hε_le1 : ε ≤ 1 := by
      dsimp only [ε]; rw [div_le_one hsqq]
      have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      simpa using Real.sqrt_le_sqrt this
    have hε2 : ε ^ 2 = 1 / (q : ℝ) := by
      dsimp only [ε]; rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hqpos)]
    have hkq_eq : ∀ k : ℕ, (k : ℝ) / (q : ℝ) = ε * ((k : ℝ) * ε) := by
      intro k; rw [show ε * ((k : ℝ) * ε) = (k : ℝ) * ε ^ 2 by ring, hε2]; ring
    have hmain_eq : mainB q = ∑ k ∈ Finset.Icc 1 (K_cut q),
        ((k : ℝ) / (q : ℝ)) * (Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
          (2 + ε ^ 2 * (((k : ℝ) * ε) ^ 6 - 3 * ((k : ℝ) * ε) ^ 4 + 3 * ((k : ℝ) * ε) ^ 2))) := by
      dsimp only [mainB]; unfold Gsum
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hkq_eq k, ← hε2]
      dsimp only [ε]
      ring
    have hsumB_split : sumB q =
        (∑ k ∈ Finset.Icc 1 (K_cut q), ((k : ℝ) / (q : ℝ)) * ((p3q q (q + k) + p3q q (q - k)) / p3q q q)) +
        (∑ k ∈ Finset.Icc (K_cut q + 1) q, ((k : ℝ) / (q : ℝ)) * ((p3q q (q + k) + p3q q (q - k)) / p3q q q)) := by
      unfold sumB
      rw [Finset.sum_div, sum_Icc_split (K := K_cut q) (by omega)]
      congr 1 <;> (refine Finset.sum_congr rfl fun k _ => by ring)
    rw [hsumB_split, hmain_eq, Real.norm_eq_abs, abs_mul, abs_of_pos hqpos]
    have hdiff_split :
        ((∑ k ∈ Finset.Icc 1 (K_cut q), ((k : ℝ) / (q : ℝ)) * ((p3q q (q + k) + p3q q (q - k)) / p3q q q)) +
          (∑ k ∈ Finset.Icc (K_cut q + 1) q, ((k : ℝ) / (q : ℝ)) * ((p3q q (q + k) + p3q q (q - k)) / p3q q q))) -
        (∑ k ∈ Finset.Icc 1 (K_cut q),
          ((k : ℝ) / (q : ℝ)) * (Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
            (2 + ε ^ 2 * (((k : ℝ) * ε) ^ 6 - 3 * ((k : ℝ) * ε) ^ 4 + 3 * ((k : ℝ) * ε) ^ 2)))) =
        (∑ k ∈ Finset.Icc 1 (K_cut q),
          ((k : ℝ) / (q : ℝ)) * (((p3q q (q + k) + p3q q (q - k)) / p3q q q) -
            Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
              (2 + ε ^ 2 * (((k : ℝ) * ε) ^ 6 - 3 * ((k : ℝ) * ε) ^ 4 + 3 * ((k : ℝ) * ε) ^ 2)))) +
        (∑ k ∈ Finset.Icc (K_cut q + 1) q, ((k : ℝ) / (q : ℝ)) * ((p3q q (q + k) + p3q q (q - k)) / p3q q q)) := by
      have : (∑ k ∈ Finset.Icc 1 (K_cut q),
          ((k : ℝ) / (q : ℝ)) * (((p3q q (q + k) + p3q q (q - k)) / p3q q q) -
            Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
              (2 + ε ^ 2 * (((k : ℝ) * ε) ^ 6 - 3 * ((k : ℝ) * ε) ^ 4 + 3 * ((k : ℝ) * ε) ^ 2)))) =
          (∑ k ∈ Finset.Icc 1 (K_cut q), ((k : ℝ) / (q : ℝ)) * ((p3q q (q + k) + p3q q (q - k)) / p3q q q)) -
          (∑ k ∈ Finset.Icc 1 (K_cut q),
            ((k : ℝ) / (q : ℝ)) * (Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
              (2 + ε ^ 2 * (((k : ℝ) * ε) ^ 6 - 3 * ((k : ℝ) * ε) ^ 4 + 3 * ((k : ℝ) * ε) ^ 2)))) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      linarith
    rw [hdiff_split]
    have hbody : |∑ k ∈ Finset.Icc 1 (K_cut q),
        ((k : ℝ) / (q : ℝ)) * (((p3q q (q + k) + p3q q (q - k)) / p3q q q) -
          Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
            (2 + ε ^ 2 * (((k : ℝ) * ε) ^ 6 - 3 * ((k : ℝ) * ε) ^ 4 + 3 * ((k : ℝ) * ε) ^ 2)))| ≤
        85000 * (3 * Real.exp 1 * (1 + (Nat.factorial 1 : ℝ)) +
          3 * Real.exp 1 * (1 + (Nat.factorial 21 : ℝ))) * ε ^ 3 := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have h1 : ∑ k ∈ Finset.Icc 1 (K_cut q),
          |((k : ℝ) / (q : ℝ)) * (((p3q q (q + k) + p3q q (q - k)) / p3q q q) -
            Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
              (2 + ε ^ 2 * (((k : ℝ) * ε) ^ 6 - 3 * ((k : ℝ) * ε) ^ 4 + 3 * ((k : ℝ) * ε) ^ 2)))| ≤
          ∑ k ∈ Finset.Icc 1 (K_cut q),
            85000 * ε ^ 5 * (((k : ℝ) * ε) ^ 1 + ((k : ℝ) * ε) ^ 21) * Real.exp (-3 * ((k : ℝ) * ε) ^ 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) / (q : ℝ)), hkq_eq k]
        have hloc := local_sum_term_approx hq (mem_Icc.mp hk).2
        have hm := mul_le_mul_of_nonneg_left hloc (by positivity : 0 ≤ ε * ((k : ℝ) * ε))
        linarith [show ε * ((k : ℝ) * ε) * (85000 * ε ^ 4 * (1 + ((k : ℝ) * ε) ^ 20) * Real.exp (-3 * ((k : ℝ) * ε) ^ 2)) =
          85000 * ε ^ 5 * (((k : ℝ) * ε) ^ 1 + ((k : ℝ) * ε) ^ 21) * Real.exp (-3 * ((k : ℝ) * ε) ^ 2) by ring]
      have h2 : ∑ k ∈ Finset.Icc 1 (K_cut q),
            85000 * ε ^ 5 * (((k : ℝ) * ε) ^ 1 + ((k : ℝ) * ε) ^ 21) * Real.exp (-3 * ((k : ℝ) * ε) ^ 2) =
          85000 * ε ^ 5 * ((∑ k ∈ Finset.Icc 1 (K_cut q), ((k : ℝ) * ε) ^ 1 * Real.exp (-3 * ((k : ℝ) * ε) ^ 2)) +
            (∑ k ∈ Finset.Icc 1 (K_cut q), ((k : ℝ) * ε) ^ 21 * Real.exp (-3 * ((k : ℝ) * ε) ^ 2))) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      have h3 := sum_pow_exp_neg_three_sq_le 1 hε_pos hε_le1 (K_cut q)
      have h4 := sum_pow_exp_neg_three_sq_le 21 hε_pos hε_le1 (K_cut q)
      rw [h2] at h1
      have h5 := mul_le_mul_of_nonneg_left (add_le_add h3 h4) (by positivity : 0 ≤ 85000 * ε ^ 5)
      have h6 : 85000 * ε ^ 5 *
          ((3 * Real.exp 1 * (1 + (Nat.factorial 1 : ℝ))) / ε +
           (3 * Real.exp 1 * (1 + (Nat.factorial 21 : ℝ))) / ε) =
          85000 * (3 * Real.exp 1 * (1 + (Nat.factorial 1 : ℝ)) +
            3 * Real.exp 1 * (1 + (Nat.factorial 21 : ℝ))) * ε ^ 4 := by
        field_simp
      have hε43 : ε ^ 4 ≤ ε ^ 3 := by
        rw [show ε ^ 4 = ε ^ 3 * ε by ring]; exact mul_le_of_le_one_right (by positivity) hε_le1
      have hC_mul := mul_le_mul_of_nonneg_left hε43
        (by positivity : 0 ≤ 85000 * (3 * Real.exp 1 * (1 + (Nat.factorial 1 : ℝ)) +
          3 * Real.exp 1 * (1 + (Nat.factorial 21 : ℝ))))
      exact le_trans h1 (le_trans h5 (by rw [h6]; exact hC_mul))
    have htail : |∑ k ∈ Finset.Icc (K_cut q + 1) q,
        ((k : ℝ) / (q : ℝ)) * ((p3q q (q + k) + p3q q (q - k)) / p3q q q)| ≤
        2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
      have hw : ∀ k ∈ Finset.Icc (K_cut q + 1) q, |(k : ℝ) / (q : ℝ)| ≤ 1 := by
        intro k hk; rw [mem_Icc] at hk
        rw [abs_of_nonneg (by positivity), div_le_one hqpos]; exact_mod_cast hk.2
      have h := abs_p3q_tail_sum_le hq (fun k => (k : ℝ) / (q : ℝ)) hw 1 (by norm_num)
      refine le_trans (le_of_eq ?_) h
      congr 1; refine Finset.sum_congr rfl fun k _ => by ring
    have hqε3 : (q : ℝ) * ε ^ 3 = ε := by
      rw [show ε ^ 3 = ε ^ 2 * ε by ring, hε2]; field_simp
    have hqtail : (q : ℝ) * (2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) * Real.sqrt (q : ℝ))) =
        2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) * ε := by
      dsimp only [ε]; field_simp
    have htri := abs_add_le
      (∑ k ∈ Finset.Icc 1 (K_cut q),
        ((k : ℝ) / (q : ℝ)) * (((p3q q (q + k) + p3q q (q - k)) / p3q q q) -
          Real.exp (-3 * ((k : ℝ) * ε) ^ 2) *
            (2 + ε ^ 2 * (((k : ℝ) * ε) ^ 6 - 3 * ((k : ℝ) * ε) ^ 4 + 3 * ((k : ℝ) * ε) ^ 2))))
      (∑ k ∈ Finset.Icc (K_cut q + 1) q, ((k : ℝ) / (q : ℝ)) * ((p3q q (q + k) + p3q q (q - k)) / p3q q q))
    have hmul := mul_le_mul_of_nonneg_left (le_trans htri (add_le_add hbody htail)) (le_of_lt hqpos)
    dsimp only [C_rem]
    calc (q : ℝ) * |_| ≤ (q : ℝ) * (85000 * (3 * Real.exp 1 * (1 + (Nat.factorial 1 : ℝ)) +
            3 * Real.exp 1 * (1 + (Nat.factorial 21 : ℝ))) * ε ^ 3 +
            2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) * Real.sqrt (q : ℝ))) := hmul
      _ = (85000 * (3 * Real.exp 1 * (1 + (Nat.factorial 1 : ℝ)) +
            3 * Real.exp 1 * (1 + (Nat.factorial 21 : ℝ))) +
            2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10)) * ε := by
          rw [mul_add, ← mul_assoc, mul_comm (q : ℝ), mul_assoc, hqε3, hqtail]; ring
      _ = (85000 * (3 * Real.exp 1 * (1 + (Nat.factorial 1 : ℝ)) +
            3 * Real.exp 1 * (1 + (Nat.factorial 21 : ℝ))) +
            2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10)) * (Real.sqrt (q : ℝ))⁻¹ := by
          dsimp only [ε]; rw [one_div]
  have hcomb := hrem_lim.add hmain_lim
  rw [add_zero] at hcomb
  refine hcomb.congr fun q => by ring

private lemma local_diff_leading_approx {q k : ℕ} (hq : 10 ^ 8 ≤ q) (hk : k ≤ K_cut q) :
    let ε := 1 / Real.sqrt (q : ℝ)
    let t := (k : ℝ) * ε
    |(p3q q (q + k) - p3q q (q - k)) / p3q q q - Real.exp (-3 * t ^ 2) * (-2 * ε * t ^ 3)| ≤
      85020 * ε ^ 3 * (1 + t ^ 20) * Real.exp (-3 * t ^ 2) := by
  intro ε t
  have hq1 : 1 ≤ q := le_trans (by norm_num) hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hsqq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
  have hε_pos : 0 < ε := by dsimp only [ε]; positivity
  have hε_le1 : ε ≤ 1 := by
    dsimp only [ε]; rw [div_le_one hsqq]
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    simpa using Real.sqrt_le_sqrt this
  have ht_nn : 0 ≤ t := by dsimp only [t]; positivity
  have hloc := local_diff_term_approx hq hk
  have hε3_poly : |ε ^ 3 * (-(1 / 3 : ℝ) * t ^ 9 + 3 * t ^ 7 - 6 * t ^ 5 + 2 * t ^ 3)| ≤
      20 * ε ^ 3 * (1 + t ^ 20) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < ε ^ 3)]
    have hpow : ∀ m ≤ 20, t ^ m ≤ 1 + t ^ 20 := fun m hm => by
      have := abs_pow_le_one_add (x := t) hm
      rwa [abs_of_nonneg ht_nn] at this
    have h3 := hpow 3 (by omega)
    have h5 := hpow 5 (by omega)
    have h7 := hpow 7 (by omega)
    have h9 := hpow 9 (by omega)
    have hp : |-(1 / 3 : ℝ) * t ^ 9 + 3 * t ^ 7 - 6 * t ^ 5 + 2 * t ^ 3| ≤ 20 * (1 + t ^ 20) := by
      rw [abs_le]
      constructor <;> linarith [pow_nonneg ht_nn 3, pow_nonneg ht_nn 5, pow_nonneg ht_nn 7, pow_nonneg ht_nn 9]
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ ε ^ 3)
    linarith [show ε ^ 3 * (20 * (1 + t ^ 20)) = 20 * ε ^ 3 * (1 + t ^ 20) by ring]
  set E1 := (p3q q (q + k) - p3q q (q - k)) / p3q q q -
      Real.exp (-3 * t ^ 2) * (-2 * ε * t ^ 3 + ε ^ 3 * (-(1 / 3 : ℝ) * t ^ 9 + 3 * t ^ 7 - 6 * t ^ 5 + 2 * t ^ 3))
  set E2 := Real.exp (-3 * t ^ 2) * (ε ^ 3 * (-(1 / 3 : ℝ) * t ^ 9 + 3 * t ^ 7 - 6 * t ^ 5 + 2 * t ^ 3))
  have hsp : (p3q q (q + k) - p3q q (q - k)) / p3q q q - Real.exp (-3 * t ^ 2) * (-2 * ε * t ^ 3) = E1 + E2 := by
    dsimp only [E1, E2]; ring
  rw [hsp]
  have htri := abs_add_le E1 E2
  have hE2 : |E2| ≤ 20 * ε ^ 3 * (1 + t ^ 20) * Real.exp (-3 * t ^ 2) := by
    dsimp only [E2]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hm := mul_le_mul_of_nonneg_left hε3_poly (le_of_lt (Real.exp_pos (-3 * t ^ 2)))
    linarith [show Real.exp (-3 * t ^ 2) * (20 * ε ^ 3 * (1 + t ^ 20)) =
      20 * ε ^ 3 * (1 + t ^ 20) * Real.exp (-3 * t ^ 2) by ring]
  have hε43 : ε ^ 4 ≤ ε ^ 3 := by
    rw [show ε ^ 4 = ε ^ 3 * ε by ring]; exact mul_le_of_le_one_right (by positivity) hε_le1
  have hE1_le : 85000 * ε ^ 4 * (1 + t ^ 20) * Real.exp (-3 * t ^ 2) ≤
      85000 * ε ^ 3 * (1 + t ^ 20) * Real.exp (-3 * t ^ 2) := by
    have hm := mul_le_mul_of_nonneg_right hε43 (by positivity : 0 ≤ (1 + t ^ 20) * Real.exp (-3 * t ^ 2))
    linarith
  linarith

/-- Asymptotic expansion of `C(q)`: `q * (sumC q - (-2/(27 q))) → 0`. -/
theorem tendsto_sumC :
    Tendsto (fun q : ℕ => (q : ℝ) * (sumC q - (-(2 / (27 * (q : ℝ)))))) atTop (𝓝 0) := by
  let mainC : ℕ → ℝ := fun q => (1 / (q : ℝ)) * (-2 * Gsum 2 q)
  have hmain_lim : Tendsto (fun q : ℕ => (q : ℝ) * (mainC q - (-(2 / (27 * (q : ℝ)))))) atTop (𝓝 0) := by
    have hG2 := tendsto_Gsum 2 (by norm_num)
    have hcomb : Tendsto (fun q : ℕ => -2 * Gsum 2 q + (2 / 27 : ℝ)) atTop (𝓝 0) := by
      have hzero : -2 * ((Nat.factorial 2 : ℝ) / (2 * (3 : ℝ) ^ (2 + 1))) + (2 / 27 : ℝ) = 0 := by
        norm_num [Nat.factorial]
      rw [← hzero]
      exact (hG2.const_mul (-2)).add (tendsto_const_nhds (x := (2 / 27 : ℝ)))
    refine hcomb.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with q hq
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    dsimp only [mainC]
    field_simp; ring
  set C_rem : ℝ := 85020 * (3 * Real.exp 1 * (1 + (Nat.factorial 2 : ℝ)) +
      3 * Real.exp 1 * (1 + (Nat.factorial 22 : ℝ))) + 2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10)
  have hrem_lim : Tendsto (fun q : ℕ => (q : ℝ) * (sumC q - mainC q)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using tendsto_inv_sqrt.const_mul C_rem)
    filter_upwards [Filter.eventually_ge_atTop (10 ^ 8)] with q hq
    have hK := K_cut_bounds hq
    have hq1 : 1 ≤ q := le_trans (by norm_num) hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
    have hsqq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
    set ε := 1 / Real.sqrt (q : ℝ)
    have hε_pos : 0 < ε := by dsimp only [ε]; positivity
    have hε_le1 : ε ≤ 1 := by
      dsimp only [ε]; rw [div_le_one hsqq]
      have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      simpa using Real.sqrt_le_sqrt this
    have hε2 : ε ^ 2 = 1 / (q : ℝ) := by
      dsimp only [ε]; rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hqpos)]
    have hkq2_eq : ∀ k : ℕ, ((k : ℝ) / (q : ℝ)) ^ 2 = ε ^ 2 * ((k : ℝ) * ε) ^ 2 := by
      intro k; rw [show ε ^ 2 * ((k : ℝ) * ε) ^ 2 = (k : ℝ) ^ 2 * (ε ^ 2) ^ 2 by ring, hε2]; ring
    have hmain_eq : mainC q = ∑ k ∈ Finset.Icc 1 (K_cut q),
        ((k : ℝ) / (q : ℝ)) ^ 2 * (Real.exp (-3 * ((k : ℝ) * ε) ^ 2) * (-2 * ε * ((k : ℝ) * ε) ^ 3)) := by
      dsimp only [mainC]; unfold Gsum
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hkq2_eq k, ← hε2]
      dsimp only [ε]
      ring
    have hsumC_split : sumC q =
        (∑ k ∈ Finset.Icc 1 (K_cut q), ((k : ℝ) / (q : ℝ)) ^ 2 * ((p3q q (q + k) - p3q q (q - k)) / p3q q q)) +
        (∑ k ∈ Finset.Icc (K_cut q + 1) q, ((k : ℝ) / (q : ℝ)) ^ 2 * ((p3q q (q + k) - p3q q (q - k)) / p3q q q)) := by
      unfold sumC
      rw [Finset.sum_div, sum_Icc_split (K := K_cut q) (by omega)]
      congr 1 <;> (refine Finset.sum_congr rfl fun k _ => by ring)
    rw [hsumC_split, hmain_eq, Real.norm_eq_abs, abs_mul, abs_of_pos hqpos]
    have hdiff_split :
        ((∑ k ∈ Finset.Icc 1 (K_cut q), ((k : ℝ) / (q : ℝ)) ^ 2 * ((p3q q (q + k) - p3q q (q - k)) / p3q q q)) +
          (∑ k ∈ Finset.Icc (K_cut q + 1) q, ((k : ℝ) / (q : ℝ)) ^ 2 * ((p3q q (q + k) - p3q q (q - k)) / p3q q q))) -
        (∑ k ∈ Finset.Icc 1 (K_cut q),
          ((k : ℝ) / (q : ℝ)) ^ 2 * (Real.exp (-3 * ((k : ℝ) * ε) ^ 2) * (-2 * ε * ((k : ℝ) * ε) ^ 3))) =
        (∑ k ∈ Finset.Icc 1 (K_cut q),
          ((k : ℝ) / (q : ℝ)) ^ 2 * (((p3q q (q + k) - p3q q (q - k)) / p3q q q) -
            Real.exp (-3 * ((k : ℝ) * ε) ^ 2) * (-2 * ε * ((k : ℝ) * ε) ^ 3))) +
        (∑ k ∈ Finset.Icc (K_cut q + 1) q, ((k : ℝ) / (q : ℝ)) ^ 2 * ((p3q q (q + k) - p3q q (q - k)) / p3q q q)) := by
      have : (∑ k ∈ Finset.Icc 1 (K_cut q),
          ((k : ℝ) / (q : ℝ)) ^ 2 * (((p3q q (q + k) - p3q q (q - k)) / p3q q q) -
            Real.exp (-3 * ((k : ℝ) * ε) ^ 2) * (-2 * ε * ((k : ℝ) * ε) ^ 3))) =
          (∑ k ∈ Finset.Icc 1 (K_cut q), ((k : ℝ) / (q : ℝ)) ^ 2 * ((p3q q (q + k) - p3q q (q - k)) / p3q q q)) -
          (∑ k ∈ Finset.Icc 1 (K_cut q),
            ((k : ℝ) / (q : ℝ)) ^ 2 * (Real.exp (-3 * ((k : ℝ) * ε) ^ 2) * (-2 * ε * ((k : ℝ) * ε) ^ 3))) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      linarith
    rw [hdiff_split]
    have hbody : |∑ k ∈ Finset.Icc 1 (K_cut q),
        ((k : ℝ) / (q : ℝ)) ^ 2 * (((p3q q (q + k) - p3q q (q - k)) / p3q q q) -
          Real.exp (-3 * ((k : ℝ) * ε) ^ 2) * (-2 * ε * ((k : ℝ) * ε) ^ 3))| ≤
        85020 * (3 * Real.exp 1 * (1 + (Nat.factorial 2 : ℝ)) +
          3 * Real.exp 1 * (1 + (Nat.factorial 22 : ℝ))) * ε ^ 3 := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have h1 : ∑ k ∈ Finset.Icc 1 (K_cut q),
          |((k : ℝ) / (q : ℝ)) ^ 2 * (((p3q q (q + k) - p3q q (q - k)) / p3q q q) -
            Real.exp (-3 * ((k : ℝ) * ε) ^ 2) * (-2 * ε * ((k : ℝ) * ε) ^ 3))| ≤
          ∑ k ∈ Finset.Icc 1 (K_cut q),
            85020 * ε ^ 5 * (((k : ℝ) * ε) ^ 2 + ((k : ℝ) * ε) ^ 22) * Real.exp (-3 * ((k : ℝ) * ε) ^ 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((k : ℝ) / (q : ℝ)) ^ 2), hkq2_eq k]
        have hcomb := local_diff_leading_approx hq (mem_Icc.mp hk).2
        have hm := mul_le_mul_of_nonneg_left hcomb (by positivity : 0 ≤ ε ^ 2 * ((k : ℝ) * ε) ^ 2)
        linarith [show ε ^ 2 * ((k : ℝ) * ε) ^ 2 *
          (85020 * ε ^ 3 * (1 + ((k : ℝ) * ε) ^ 20) * Real.exp (-3 * ((k : ℝ) * ε) ^ 2)) =
          85020 * ε ^ 5 * (((k : ℝ) * ε) ^ 2 + ((k : ℝ) * ε) ^ 22) * Real.exp (-3 * ((k : ℝ) * ε) ^ 2) by ring]
      have h2 : ∑ k ∈ Finset.Icc 1 (K_cut q),
            85020 * ε ^ 5 * (((k : ℝ) * ε) ^ 2 + ((k : ℝ) * ε) ^ 22) * Real.exp (-3 * ((k : ℝ) * ε) ^ 2) =
          85020 * ε ^ 5 * ((∑ k ∈ Finset.Icc 1 (K_cut q), ((k : ℝ) * ε) ^ 2 * Real.exp (-3 * ((k : ℝ) * ε) ^ 2)) +
            (∑ k ∈ Finset.Icc 1 (K_cut q), ((k : ℝ) * ε) ^ 22 * Real.exp (-3 * ((k : ℝ) * ε) ^ 2))) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      have h3 := sum_pow_exp_neg_three_sq_le 2 hε_pos hε_le1 (K_cut q)
      have h4 := sum_pow_exp_neg_three_sq_le 22 hε_pos hε_le1 (K_cut q)
      rw [h2] at h1
      have h5 := mul_le_mul_of_nonneg_left (add_le_add h3 h4) (by positivity : 0 ≤ 85020 * ε ^ 5)
      have h6 : 85020 * ε ^ 5 *
          ((3 * Real.exp 1 * (1 + (Nat.factorial 2 : ℝ))) / ε +
           (3 * Real.exp 1 * (1 + (Nat.factorial 22 : ℝ))) / ε) =
          85020 * (3 * Real.exp 1 * (1 + (Nat.factorial 2 : ℝ)) +
            3 * Real.exp 1 * (1 + (Nat.factorial 22 : ℝ))) * ε ^ 4 := by
        field_simp
      have hε43 : ε ^ 4 ≤ ε ^ 3 := by
        rw [show ε ^ 4 = ε ^ 3 * ε by ring]; exact mul_le_of_le_one_right (by positivity) hε_le1
      have hC_mul := mul_le_mul_of_nonneg_left hε43
        (by positivity : 0 ≤ 85020 * (3 * Real.exp 1 * (1 + (Nat.factorial 2 : ℝ)) +
          3 * Real.exp 1 * (1 + (Nat.factorial 22 : ℝ))))
      exact le_trans h1 (le_trans h5 (by rw [h6]; exact hC_mul))
    have htail : |∑ k ∈ Finset.Icc (K_cut q + 1) q,
        ((k : ℝ) / (q : ℝ)) ^ 2 * ((p3q q (q + k) - p3q q (q - k)) / p3q q q)| ≤
        2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
      have hw : ∀ k ∈ Finset.Icc (K_cut q + 1) q, |((k : ℝ) / (q : ℝ)) ^ 2| ≤ 1 := by
        intro k hk; rw [mem_Icc] at hk
        rw [abs_of_nonneg (by positivity)]
        have h1 : (k : ℝ) / (q : ℝ) ≤ 1 := (div_le_one hqpos).mpr (by exact_mod_cast hk.2)
        exact pow_le_one₀ (by positivity) h1 (n := 2)
      have h := abs_p3q_tail_sum_le hq (fun k => ((k : ℝ) / (q : ℝ)) ^ 2) hw (-1) (by norm_num)
      refine le_trans (le_of_eq ?_) h
      congr 1; refine Finset.sum_congr rfl fun k _ => by ring
    have hqε3 : (q : ℝ) * ε ^ 3 = ε := by
      rw [show ε ^ 3 = ε ^ 2 * ε by ring, hε2]; field_simp
    have hqtail : (q : ℝ) * (2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) * Real.sqrt (q : ℝ))) =
        2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) * ε := by
      dsimp only [ε]; field_simp
    have htri := abs_add_le
      (∑ k ∈ Finset.Icc 1 (K_cut q),
        ((k : ℝ) / (q : ℝ)) ^ 2 * (((p3q q (q + k) - p3q q (q - k)) / p3q q q) -
          Real.exp (-3 * ((k : ℝ) * ε) ^ 2) * (-2 * ε * ((k : ℝ) * ε) ^ 3)))
      (∑ k ∈ Finset.Icc (K_cut q + 1) q, ((k : ℝ) / (q : ℝ)) ^ 2 * ((p3q q (q + k) - p3q q (q - k)) / p3q q q))
    have hmul := mul_le_mul_of_nonneg_left (le_trans htri (add_le_add hbody htail)) (le_of_lt hqpos)
    dsimp only [C_rem]
    calc (q : ℝ) * |_| ≤ (q : ℝ) * (85020 * (3 * Real.exp 1 * (1 + (Nat.factorial 2 : ℝ)) +
            3 * Real.exp 1 * (1 + (Nat.factorial 22 : ℝ))) * ε ^ 3 +
            2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10) / ((q : ℝ) * Real.sqrt (q : ℝ))) := hmul
      _ = (85020 * (3 * Real.exp 1 * (1 + (Nat.factorial 2 : ℝ)) +
            3 * Real.exp 1 * (1 + (Nat.factorial 22 : ℝ))) +
            2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10)) * ε := by
          rw [mul_add, ← mul_assoc, mul_comm (q : ℝ), mul_assoc, hqε3, hqtail]; ring
      _ = (85020 * (3 * Real.exp 1 * (1 + (Nat.factorial 2 : ℝ)) +
            3 * Real.exp 1 * (1 + (Nat.factorial 22 : ℝ))) +
            2 * ((Nat.factorial 10 : ℝ) * 3 ^ 10)) * (Real.sqrt (q : ℝ))⁻¹ := by
          dsimp only [ε]; rw [one_div]
  have hcomb := hrem_lim.add hmain_lim
  rw [add_zero] at hcomb
  refine hcomb.congr fun q => by ring

end MultinomialTV
