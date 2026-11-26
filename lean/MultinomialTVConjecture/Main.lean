/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public import MultinomialTVConjecture.Combinatorial
public import MultinomialTVConjecture.StirlingRefined
public import MultinomialTVConjecture.LocalAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Main Assembly and Resolution of Conjecture 7.7

Proves the verbatim nested-sum fidelity identity `hAdj_eq_nested_sum`, the residue-class `1/L`
limits `tendsto_hAdj_mod0`, `tendsto_hAdj_mod1`, `tendsto_hAdj_mod2`, the complete resolution
`conjecture_7_7` (`d_0`, `a_△`, `γ_2`, cosine decomposition), and the linear and cyclic
algebraic variance closed forms `gamma_closed_form` and `gamma_cyclic_closed_form`.
-/

@[expose] public section

open scoped BigOperators
open Real Filter Topology Finset

namespace MultinomialTV

/-! ### Fidelity check: `hAdj L` matches the exact nested multinomial sum -/

/-- Exact nested-sum form of `hAdj L = E[|X_2 - X_1| |X_3 - X_2|]` under `Mult(L; 1/3, 1/3, 1/3)`. -/
theorem hAdj_eq_nested_sum (L : ℕ) :
    hAdj L = (3 : ℝ)⁻¹ ^ L *
      ∑ x1 ∈ Finset.range (L + 1), ∑ x2 ∈ Finset.range (L - x1 + 1),
        ((L.factorial : ℝ) / ((x1.factorial : ℝ) * (x2.factorial : ℝ) * ((L - x1 - x2).factorial : ℝ))) *
          |(x2 : ℝ) - (x1 : ℝ)| * |((L - x1 - x2 : ℕ) : ℝ) - (x2 : ℝ)| := by
  unfold hAdj
  congr 1
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun t _ => ⟨t.1, t.2.1⟩) ?_ ?_ ?_ ?_
  · intro ⟨a, b, c⟩ ht
    rw [mem_simplex3_mk] at ht
    simp only [mem_sigma, mem_range]; omega
  · intro ⟨a1, b1, c1⟩ ht1 ⟨a2, b2, c2⟩ ht2 h
    rw [mem_simplex3_mk] at ht1 ht2
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Prod.mk.injEq]; exact ⟨trivial, trivial, by omega⟩
  · intro ⟨a, b⟩ h
    simp only [mem_sigma, mem_range] at h
    refine ⟨(a, b, L - a - b), mem_simplex3_mk.mpr (by omega), rfl⟩
  · intro ⟨a, b, c⟩ ht
    rw [mem_simplex3_mk] at ht
    have hc : L - a - b = c := by omega
    dsimp only
    rw [hc]
    unfold T
    ring

/-! ### Constants from Banić & Elezović (arXiv:2610.17046v1, Section 7.2) -/

/-- Linear slope `c_L = 2√3 / (3π) + 1/9` of `h_adj(L)`. -/
noncomputable def cL : ℝ := 2 * Real.sqrt 3 / (3 * Real.pi) + 1 / 9

/-- Constant term `a_* = -2√3 / (9π)` of `h_adj(L)`. -/
noncomputable def aStar : ℝ := -(2 * Real.sqrt 3 / (9 * Real.pi))

/-- Residue-class `1/L` limit `b_r = lim_{L → ∞, L ≡ r (mod 3)} L (h_adj(L) - c_L L - a_*)`
(Lemma 7.3 of arXiv:2610.17046v1). -/
noncomputable def bRes (r : ℕ) : ℝ :=
  limUnder atTop (fun q : ℕ =>
    ((3 * q + r : ℕ) : ℝ) * (hAdj (3 * q + r) - cL * ((3 * q + r : ℕ) : ℝ) - aStar))

/-- Mean residue constant `d_0 = (b_0 + b_1 + b_2) / 3`. -/
noncomputable def d0 : ℝ := (bRes 0 + bRes 1 + bRes 2) / 3

/-- Adjacent triangular-lattice second-order constant `a_△ = 1/32 + (π/9)(b_0 + b_1 + b_2)`
(Definition 7.4 / eq. (7.3) of arXiv:2610.17046v1). -/
noncomputable def aTriangle : ℝ := 1 / 32 + Real.pi / 9 * (bRes 0 + bRes 1 + bRes 2)

/-- Leading quadratic coefficient `γ_2 = (64 a_△ - 3) / (32π)` of `γ(n)`
(Theorem 7.6 of arXiv:2610.17046v1). -/
noncomputable def gamma2 : ℝ := (64 * aTriangle - 3) / (32 * Real.pi)

/-! ### Central probability remainder and joint zero-limit tuple -/

private noncomputable def Sconst : ℝ := Real.sqrt 3 / (2 * Real.pi)

private lemma p3q_center_eq_div (q : ℕ) :
    p3q q q = ((3 * q).factorial : ℝ) / ((3 : ℝ) ^ (3 * q) * (q.factorial : ℝ) ^ 3) := by
  rw [p3q_eq_of_le (by omega)]
  have h1 : 3 * q - 2 * q = q := by omega
  rw [h1]
  unfold T
  ring

private noncomputable def rP (q : ℕ) : ℝ :=
  (q : ℝ) ^ 2 * ((q : ℝ) * p3q q q - Sconst * (1 - 2 / (9 * (q : ℝ)) + 2 / (81 * (q : ℝ) ^ 2)))

private noncomputable def eA (q : ℕ) : ℝ :=
  (q : ℝ) * (sumA q - (-(1 / 9 : ℝ) - 4 / (243 * (q : ℝ))))

private noncomputable def eB (q : ℕ) : ℝ :=
  (q : ℝ) * (sumB q - (1 / 3 - 2 / (27 * (q : ℝ))))

private noncomputable def eC (q : ℕ) : ℝ :=
  (q : ℝ) * (sumC q - (-(2 / (27 * (q : ℝ)))))

private lemma tendsto_rP : Tendsto rP atTop (𝓝 0) := by
  have hlim : Tendsto (fun q : ℕ => Sconst / (q : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 2] with q hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hst := p3q_center_expansion q hq
  rw [← p3q_center_eq_div q] at hst
  have hpref : Real.sqrt 3 / (2 * Real.pi * (q : ℝ)) = Sconst / (q : ℝ) := by
    unfold Sconst; ring
  rw [hpref] at hst
  rw [Real.norm_eq_abs]
  unfold rP
  have hrew : (q : ℝ) ^ 2 * ((q : ℝ) * p3q q q - Sconst * (1 - 2 / (9 * (q : ℝ)) + 2 / (81 * (q : ℝ) ^ 2))) =
      (q : ℝ) ^ 3 * (p3q q q - Sconst / (q : ℝ) * (1 - 2 / (9 * (q : ℝ)) + 2 / (81 * (q : ℝ) ^ 2))) := by
    field_simp
  rw [hrew, abs_mul, abs_of_pos (by positivity : 0 < (q : ℝ) ^ 3)]
  have hmul := mul_le_mul_of_nonneg_left hst (by positivity : 0 ≤ (q : ℝ) ^ 3)
  have heq : (q : ℝ) ^ 3 * (Sconst / (q : ℝ) * (1 / (q : ℝ) ^ 3)) = Sconst / (q : ℝ) := by
    field_simp
  linarith

private lemma tendsto_err_tuple :
    Tendsto (fun q : ℕ => ((q : ℝ)⁻¹, rP q, eA q, eB q, eC q)) atTop (𝓝 (0, 0, 0, 0, 0)) := by
  have hinv : Tendsto (fun q : ℕ => (q : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  exact hinv.prodMk_nhds (tendsto_rP.prodMk_nhds
    (tendsto_sumA.prodMk_nhds (tendsto_sumB.prodMk_nhds tendsto_sumC)))

private lemma p3q_of_rP {q : ℕ} (hq : 1 ≤ q) :
    p3q q q = Sconst * (q : ℝ)⁻¹ * (1 - 2 / 9 * (q : ℝ)⁻¹ + 2 / 81 * (q : ℝ)⁻¹ ^ 2) +
      rP q * (q : ℝ)⁻¹ ^ 3 := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  unfold rP; field_simp; ring

private lemma sumA_of_eA {q : ℕ} (hq : 1 ≤ q) :
    sumA q = -(1 / 9 : ℝ) - 4 / 243 * (q : ℝ)⁻¹ + eA q * (q : ℝ)⁻¹ := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  unfold eA; field_simp; ring

private lemma sumB_of_eB {q : ℕ} (hq : 1 ≤ q) :
    sumB q = 1 / 3 - 2 / 27 * (q : ℝ)⁻¹ + eB q * (q : ℝ)⁻¹ := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  unfold eB; field_simp; ring

private lemma sumC_of_eC {q : ℕ} (hq : 1 ≤ q) :
    sumC q = -(2 / 27 : ℝ) * (q : ℝ)⁻¹ + eC q * (q : ℝ)⁻¹ := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  unfold eC; field_simp; ring

private lemma cL_eq_Sconst : cL = 4 / 3 * Sconst + 1 / 9 := by
  unfold cL Sconst; ring

private lemma aStar_eq_Sconst : aStar = -(4 / 9 * Sconst) := by
  unfold aStar Sconst; ring

/-! ### Exact residue-class limits for `L ≡ 0, 1, 2 (mod 3)` -/

private noncomputable def polyMod0 (p : ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ :=
  let u := p.1; let r := p.2.1; let a := p.2.2.1; let b := p.2.2.2.1
  6 * Sconst * a - 12 * Sconst * b + 64 * Sconst / 81 + 12 * r +
  u ^ 2 * (4 * Sconst * a / 27 - 8 * Sconst * b / 27 + 128 * Sconst / 6561 +
    6 * a * r - 12 * b * r + 64 * r / 81) +
  u * (-(4 * Sconst * a / 3) + 8 * Sconst * b / 3 - 104 * Sconst / 729 + 4 * r / 3)

private noncomputable def polyMod1 (p : ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ :=
  let u := p.1; let r := p.2.1; let a := p.2.2.1
  6 * Sconst * a - 44 * Sconst / 81 + 12 * r +
  u ^ 4 * (4 * Sconst * a / 243 - 16 * Sconst / 59049 + 2 * a * r / 3 - 8 * r / 729) +
  u ^ 3 * (-(4 * Sconst * a / 81) + 88 * Sconst / 19683 + 4 * a * r + 20 * r / 243) +
  u ^ 2 * (-(2 * Sconst * a / 27) + 152 * Sconst / 6561 + 6 * a * r + 172 * r / 81) +
  u * (8 * Sconst * a / 3 - 116 * Sconst / 729 + 28 * r / 3)

private noncomputable def polyMod2 (p : ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ :=
  let u := p.1; let r := p.2.1; let a := p.2.2.1; let b := p.2.2.2.1; let c := p.2.2.2.2
  6 * Sconst * a - 24 * Sconst * b + 24 * Sconst * c - 44 * Sconst / 81 + 12 * r +
  u ^ 4 * (4 * Sconst * a / 81 - 8 * Sconst * b / 81 + 128 * Sconst / 19683 +
    2 * a * r - 4 * b * r + 64 * r / 243) +
  u ^ 3 * (-(52 * Sconst * a / 81) + 112 * Sconst * b / 81 - 16 * Sconst * c / 81 -
    1304 * Sconst / 19683 - 8 * a * r + 20 * b * r - 8 * c * r - 76 * r / 243) +
  u ^ 2 * (106 * Sconst * a / 27 - 244 * Sconst * b / 27 + 64 * Sconst * c / 27 +
    2096 * Sconst / 6561 + 6 * a * r - 24 * b * r + 24 * c * r - 44 * r / 81) +
  u * (-(28 * Sconst * a / 3) + 76 * Sconst * b / 3 - 40 * Sconst * c / 3 -
    260 * Sconst / 729 - 20 * r / 3)

private lemma continuous_polyMod0 : Continuous polyMod0 := by unfold polyMod0; fun_prop
private lemma continuous_polyMod1 : Continuous polyMod1 := by unfold polyMod1; fun_prop
private lemma continuous_polyMod2 : Continuous polyMod2 := by unfold polyMod2; fun_prop

/-- Residue class `L ≡ 0 (mod 3)`: `lim_{q → ∞} 3q (h_adj(3q) - c_L (3q) - a_*) = 32√3 / (81π)`. -/
theorem tendsto_hAdj_mod0 :
    Tendsto (fun q : ℕ =>
      ((3 * q + 0 : ℕ) : ℝ) * (hAdj (3 * q + 0) - cL * ((3 * q + 0 : ℕ) : ℝ) - aStar))
      atTop (𝓝 (32 * Real.sqrt 3 / (81 * Real.pi))) := by
  have hlim : Tendsto (fun q : ℕ => polyMod0 ((q : ℝ)⁻¹, rP q, eA q, eB q, eC q))
      atTop (𝓝 (polyMod0 (0, 0, 0, 0, 0))) :=
    continuous_polyMod0.continuousAt.tendsto.comp tendsto_err_tuple
  have hval : polyMod0 (0, 0, 0, 0, 0) = 32 * Real.sqrt 3 / (81 * Real.pi) := by
    unfold polyMod0 Sconst; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with q hq
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  simp only [add_zero]
  rw [hAdj_mod0 q hq, p3q_of_rP hq, sumA_of_eA hq, sumB_of_eB hq, cL_eq_Sconst, aStar_eq_Sconst]
  unfold polyMod0
  push_cast
  field_simp; ring

/-- Residue class `L ≡ 1 (mod 3)`: `lim_{q → ∞} (3q+1) (h_adj(3q+1) - c_L (3q+1) - a_*) = -22√3 / (81π)`. -/
theorem tendsto_hAdj_mod1 :
    Tendsto (fun q : ℕ =>
      ((3 * q + 1 : ℕ) : ℝ) * (hAdj (3 * q + 1) - cL * ((3 * q + 1 : ℕ) : ℝ) - aStar))
      atTop (𝓝 (-(22 * Real.sqrt 3 / (81 * Real.pi)))) := by
  have hlim : Tendsto (fun q : ℕ => polyMod1 ((q : ℝ)⁻¹, rP q, eA q, eB q, eC q))
      atTop (𝓝 (polyMod1 (0, 0, 0, 0, 0))) :=
    continuous_polyMod1.continuousAt.tendsto.comp tendsto_err_tuple
  have hval : polyMod1 (0, 0, 0, 0, 0) = -(22 * Real.sqrt 3 / (81 * Real.pi)) := by
    unfold polyMod1 Sconst; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with q hq
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  rw [hAdj_mod1 q hq, p3q_of_rP hq, sumA_of_eA hq, cL_eq_Sconst, aStar_eq_Sconst]
  unfold polyMod1
  push_cast
  field_simp; ring

/-- Residue class `L ≡ 2 (mod 3)`: `lim_{q → ∞} (3q+2) (h_adj(3q+2) - c_L (3q+2) - a_*) = -22√3 / (81π)`. -/
theorem tendsto_hAdj_mod2 :
    Tendsto (fun q : ℕ =>
      ((3 * q + 2 : ℕ) : ℝ) * (hAdj (3 * q + 2) - cL * ((3 * q + 2 : ℕ) : ℝ) - aStar))
      atTop (𝓝 (-(22 * Real.sqrt 3 / (81 * Real.pi)))) := by
  have hlim_sub : Tendsto (fun q : ℕ =>
      ((3 * q - 1 : ℕ) : ℝ) * (hAdj (3 * q - 1) - cL * ((3 * q - 1 : ℕ) : ℝ) - aStar))
      atTop (𝓝 (-(22 * Real.sqrt 3 / (81 * Real.pi)))) := by
    have hlim : Tendsto (fun q : ℕ => polyMod2 ((q : ℝ)⁻¹, rP q, eA q, eB q, eC q))
        atTop (𝓝 (polyMod2 (0, 0, 0, 0, 0))) :=
      continuous_polyMod2.continuousAt.tendsto.comp tendsto_err_tuple
    have hval : polyMod2 (0, 0, 0, 0, 0) = -(22 * Real.sqrt 3 / (81 * Real.pi)) := by
      unfold polyMod2 Sconst; ring
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with q hq
    have hq1 : 1 ≤ q := by omega
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hcast : ((3 * q - 1 : ℕ) : ℝ) = 3 * (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hAdj_mod2 q hq, hcast, p3q_of_rP hq1, sumA_of_eA hq1, sumB_of_eB hq1, sumC_of_eC hq1,
        cL_eq_Sconst, aStar_eq_Sconst]
    unfold polyMod2
    field_simp; ring
  have hshift := hlim_sub.comp (tendsto_add_atTop_nat 1)
  refine hshift.congr fun q => ?_
  have heq : 3 * (q + 1) - 1 = 3 * q + 2 := by omega
  simp only [Function.comp_apply, heq]

/-! ### Proof of Conjecture 7.7 (Banić & Elezović, arXiv:2610.17046v1) -/

theorem bRes_zero : bRes 0 = 32 * Real.sqrt 3 / (81 * Real.pi) :=
  tendsto_hAdj_mod0.limUnder_eq

theorem bRes_one : bRes 1 = -(22 * Real.sqrt 3 / (81 * Real.pi)) :=
  tendsto_hAdj_mod1.limUnder_eq

theorem bRes_two : bRes 2 = -(22 * Real.sqrt 3 / (81 * Real.pi)) :=
  tendsto_hAdj_mod2.limUnder_eq

theorem conjecture_7_7_d0 : d0 = -(4 * Real.sqrt 3 / (81 * Real.pi)) := by
  unfold d0
  rw [bRes_zero, bRes_one, bRes_two]
  ring

theorem bRes_cosine_formula (r : ℕ) (hr : r = 0 ∨ r = 1 ∨ r = 2) :
    bRes r = d0 + 4 * Real.sqrt 3 / (9 * Real.pi) * Real.cos (2 * Real.pi * (r : ℝ) / 3) := by
  rw [conjecture_7_7_d0]
  rcases hr with rfl | rfl | rfl
  · rw [bRes_zero]
    have hcos : Real.cos (2 * Real.pi * (0 : ℕ) / 3) = 1 := by simp
    rw [hcos]; ring
  · rw [bRes_one]
    have hcos : Real.cos (2 * Real.pi * (1 : ℕ) / 3) = -(1 / 2) := by
      rw [Nat.cast_one, mul_one, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]
    rw [hcos]; ring
  · rw [bRes_two]
    have hcos : Real.cos (2 * Real.pi * (2 : ℕ) / 3) = -(1 / 2) := by
      rw [Nat.cast_ofNat, show 2 * Real.pi * 2 / 3 = Real.pi + Real.pi / 3 by ring,
          Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
      ring
    rw [hcos]; ring

theorem conjecture_7_7_aTriangle : aTriangle = 1 / 32 - 4 * Real.sqrt 3 / 243 := by
  unfold aTriangle
  rw [bRes_zero, bRes_one, bRes_two]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp; ring

theorem conjecture_7_7_gamma2 :
    gamma2 = -(1 / (32 * Real.pi)) - 8 * Real.sqrt 3 / (243 * Real.pi) := by
  unfold gamma2
  rw [conjecture_7_7_aTriangle]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp; ring

/-- Complete resolution of Conjecture 7.7 (`conj:atriangle`) of Banić & Elezović,
*Discrete total variation under the multinomial, Part 2: variance under the uniform null*,
arXiv:2610.17046v1 (2026). -/
theorem conjecture_7_7 :
    aTriangle = 1 / 32 - 4 * Real.sqrt 3 / 243 ∧
    gamma2 = -(1 / (32 * Real.pi)) - 8 * Real.sqrt 3 / (243 * Real.pi) ∧
    d0 = -(4 * Real.sqrt 3 / (81 * Real.pi)) ∧
    bRes 0 = 32 * Real.sqrt 3 / (81 * Real.pi) ∧
    bRes 1 = -(22 * Real.sqrt 3 / (81 * Real.pi)) ∧
    bRes 2 = -(22 * Real.sqrt 3 / (81 * Real.pi)) ∧
    (∀ r ∈ ({0, 1, 2} : Finset ℕ),
      bRes r = d0 + 4 * Real.sqrt 3 / (9 * Real.pi) * Real.cos (2 * Real.pi * (r : ℝ) / 3)) := by
  refine ⟨conjecture_7_7_aTriangle, conjecture_7_7_gamma2, conjecture_7_7_d0,
    bRes_zero, bRes_one, bRes_two, fun r hr => ?_⟩
  simp only [mem_insert, mem_singleton] at hr
  exact bRes_cosine_formula r hr

/-- Unconditional consequence of Conjecture 7.7 + Theorem 7.6 (arXiv:2610.17046v1, p. 35):
closed form of the second-order variance coefficient `γ(n)` for `n ≥ 5`. -/
theorem gamma_closed_form (n : ℝ) (hn : n ≠ 0) :
    let p1 := (n ^ 2 - 4 * n - 4) / (32 * Real.pi * n)
    let q1 := aTriangle * n / Real.pi - (n + 1) / (8 * Real.pi * n)
    let r1 := -((n + 1) / (8 * Real.pi * n))
    (n - 1) * p1 + 2 * (n - 2) * q1 + (n - 2) * (n - 3) * r1 =
      -(n * (n + 1) / (32 * Real.pi)) - 8 * Real.sqrt 3 * n * (n - 2) / (243 * Real.pi) +
        (n - 1) / (8 * Real.pi * n) := by
  dsimp only
  rw [conjecture_7_7_aTriangle]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp; ring

/-- Unconditional consequence for Part 5 (arXiv:2611.14735v1, Theorem 5.2):
closed form of the cyclic second-order variance coefficient `γ_c(n)` for `n ≥ 5`. -/
theorem gamma_cyclic_closed_form (n : ℝ) (hn : n ≠ 0) :
    let p1 := (n ^ 2 - 4 * n - 4) / (32 * Real.pi * n)
    let q1 := aTriangle * n / Real.pi - (n + 1) / (8 * Real.pi * n)
    let r1 := -((n + 1) / (8 * Real.pi * n))
    n * p1 + 2 * n * q1 + n * (n - 3) * r1 =
      -(n * (n + 4) / (32 * Real.pi)) - 8 * Real.sqrt 3 * n ^ 2 / (243 * Real.pi) := by
  dsimp only
  rw [conjecture_7_7_aTriangle]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp; ring

/-- Unconditional degenerate small-bin formula `γ(3; N)` (Part 2, §7.2; Corollary 1.2(iii)):
combines the static `n = 3` block `2 p_1(3) + 2 q_1(3)` with the oscillating residue
contribution `2 (b_{N mod 3} - d_0)`. -/
theorem gamma3_closed_form (N : ℕ) :
    let n : ℝ := 3
    let p1 := (n ^ 2 - 4 * n - 4) / (32 * Real.pi * n)
    let q1 := aTriangle * n / Real.pi - (n + 1) / (8 * Real.pi * n)
    2 * p1 + 2 * q1 + 2 * (bRes (N % 3) - d0) =
      -(7 / (24 * Real.pi)) - 8 * Real.sqrt 3 / (81 * Real.pi) +
        8 * Real.sqrt 3 / (9 * Real.pi) * Real.cos (2 * Real.pi * (N : ℝ) / 3) := by
  dsimp only
  have hr : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2 := by omega
  have hbr := bRes_cosine_formula (N % 3) hr
  have hdiv : (N : ℝ) = 3 * ((N / 3 : ℕ) : ℝ) + ((N % 3 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N 3).symm
  have hcos :
      Real.cos (2 * Real.pi * ((N % 3 : ℕ) : ℝ) / 3) = Real.cos (2 * Real.pi * (N : ℝ) / 3) := by
    have harg :
        2 * Real.pi * (N : ℝ) / 3 =
          2 * Real.pi * ((N % 3 : ℕ) : ℝ) / 3 + ((N / 3 : ℕ) : ℝ) * (2 * Real.pi) := by
      rw [hdiv]; ring
    rw [harg, Real.cos_add_nat_mul_two_pi]
  rw [hbr, hcos, conjecture_7_7_aTriangle]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp; ring

/-- Unconditional degenerate small-bin formula `γ(4; N)` (Part 2, §8; Corollary 1.2(iii)):
combines the static `n = 4` block `3 p_1(4) + 4 q_1(4) + 2 r_1(4)` with the bipartite
parity term `(-1)^N / (2π)`. -/
theorem gamma4_closed_form (N : ℕ) :
    let n : ℝ := 4
    let p1 := (n ^ 2 - 4 * n - 4) / (32 * Real.pi * n)
    let q1 := aTriangle * n / Real.pi - (n + 1) / (8 * Real.pi * n)
    let r1 := -((n + 1) / (8 * Real.pi * n))
    3 * p1 + 4 * q1 + 2 * r1 + (-1 : ℝ) ^ N / (2 * Real.pi) =
      -(17 / (32 * Real.pi)) - 64 * Real.sqrt 3 / (243 * Real.pi) +
        (-1 : ℝ) ^ N / (2 * Real.pi) := by
  dsimp only
  rw [conjecture_7_7_aTriangle]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp; ring

end MultinomialTV

end
