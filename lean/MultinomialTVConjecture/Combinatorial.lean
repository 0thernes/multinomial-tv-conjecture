import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open scoped BigOperators
open Finset

namespace MultinomialTV

/-- Reciprocal product of three factorials: `1 / (a! b! c!)`. -/
noncomputable def T (a b c : ℕ) : ℝ :=
  ((a.factorial : ℝ) * (b.factorial : ℝ) * (c.factorial : ℝ))⁻¹

lemma T_pos (a b c : ℕ) : 0 < T a b c := by
  unfold T; positivity

lemma T_symm_12 (a b c : ℕ) : T a b c = T b a c := by unfold T; ring
lemma T_symm_23 (a b c : ℕ) : T a b c = T a c b := by unfold T; ring
lemma T_symm_cyc (a b c : ℕ) : T a b c = T b c a := by unfold T; ring
lemma T_symm_13 (a b c : ℕ) : T a b c = T c b a := by unfold T; ring

lemma mul_T_fst (a b c : ℕ) : ((a + 1 : ℕ) : ℝ) * T (a + 1) b c = T a b c := by
  unfold T
  rw [Nat.factorial_succ]
  have h1 : ((a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : (a.factorial : ℝ) ≠ 0 := by positivity
  have h3 : (b.factorial : ℝ) ≠ 0 := by positivity
  have h4 : (c.factorial : ℝ) ≠ 0 := by positivity
  push_cast; field_simp

lemma mul_T_snd (a b c : ℕ) : ((b + 1 : ℕ) : ℝ) * T a (b + 1) c = T a b c := by
  rw [T_symm_12, mul_T_fst, T_symm_12]

lemma mul_T_thd (a b c : ℕ) : ((c + 1 : ℕ) : ℝ) * T a b (c + 1) = T a b c := by
  rw [T_symm_23, mul_T_snd, T_symm_23]

/-- The 3-part discrete simplex `{(x1, x2, x3) ∈ ℕ³ : x1 + x2 + x3 = L}`. -/
def simplex3 (L : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (L + 1)) ×ˢ ((Finset.range (L + 1)) ×ˢ (Finset.range (L + 1)))).filter
    (fun t => t.1 + t.2.1 + t.2.2 = L)

lemma mem_simplex3 {L : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ simplex3 L ↔ t.1 + t.2.1 + t.2.2 = L := by
  simp only [simplex3, mem_filter, mem_product, mem_range]
  constructor
  · exact fun h => h.2
  · intro h; refine ⟨⟨by omega, by omega, by omega⟩, h⟩

lemma mem_simplex3_mk {L a b c : ℕ} :
    (a, b, c) ∈ simplex3 L ↔ a + b + c = L := mem_simplex3

/-- The exact adjacent skeleton `h_adj(L) = E[|X_2 - X_1| |X_3 - X_2|]` under `Mult(L; 1/3, 1/3, 1/3)`
(Banić & Elezović, arXiv:2610.17046v1, eq. (5.1) / Section 7.2). -/
noncomputable def hAdj (L : ℕ) : ℝ :=
  (3 : ℝ)⁻¹ ^ L * ∑ t ∈ simplex3 L,
    ((L.factorial : ℝ) * T t.1 t.2.1 t.2.2) *
      |(t.2.1 : ℝ) - (t.1 : ℝ)| * |(t.2.2 : ℝ) - (t.2.1 : ℝ)|

/-- The trinomial probability `P(X_1 = X_2 = x, X_3 = 3q - 2x)` under `Mult(3q; 1/3, 1/3, 1/3)`. -/
noncomputable def p3q (q x : ℕ) : ℝ :=
  if 2 * x ≤ 3 * q then
    ((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q) * T x x (3 * q - 2 * x)
  else 0

lemma p3q_center_pos (q : ℕ) : 0 < p3q q q := by
  unfold p3q
  rw [ite_eq_left (by omega)]
  have hT := T_pos q q (3 * q - 2 * q)
  positivity

/-- The first normalized 1D central sum `A(q)`. -/
noncomputable def sumA (q : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 q, (p3q q (q + k) - p3q q (q - k))) / p3q q q

/-- The second normalized 1D central sum `B(q)`. -/
noncomputable def sumB (q : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 q, ((k : ℝ) / (q : ℝ)) * (p3q q (q + k) + p3q q (q - k))) / p3q q q

/-- The third normalized 1D central sum `C(q)`. -/
noncomputable def sumC (q : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 q, (((k : ℝ) / (q : ℝ)) ^ 2) * (p3q q (q + k) - p3q q (q - k))) / p3q q q

/-! ### Part 1: Multinomial sum, symmetries, and second-moment identities on `simplex3 L` -/

lemma sum_simplex3_T (L : ℕ) :
    ∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 = (3 : ℝ) ^ L / (L.factorial : ℝ) := by
  have h1 : ∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 =
      ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L - a + 1), T a b (L - a - b) := by
    rw [Finset.sum_sigma']
    refine Finset.sum_bij (fun t _ => ⟨t.1, t.2.1⟩) ?_ ?_ ?_ ?_
    · intro ⟨a, b, c⟩ ht; rw [mem_simplex3] at ht; simp only [mem_sigma, mem_range] at ht ⊢; omega
    · intro ⟨a1, b1, c1⟩ ht1 ⟨a2, b2, c2⟩ ht2 h
      rw [mem_simplex3_mk] at ht1 ht2
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Prod.mk.injEq]; exact ⟨trivial, trivial, by omega⟩
    · intro ⟨a, b⟩ h
      simp only [mem_sigma, mem_range] at h
      refine ⟨(a, b, L - a - b), ?_, rfl⟩
      rw [mem_simplex3]; dsimp only; omega
    · intro ⟨a, b, c⟩ ht
      rw [mem_simplex3] at ht; dsimp only at ht ⊢
      have hc : L - a - b = c := by omega
      rw [hc]
  rw [h1]
  have hinner : ∀ a ≤ L,
      ∑ b ∈ Finset.range (L - a + 1), T a b (L - a - b) =
        (a.factorial : ℝ)⁻¹ * ((2 : ℝ) ^ (L - a) / ((L - a).factorial : ℝ)) := by
    intro a ha
    have hbinom := add_pow (1 : ℝ) (1 : ℝ) (L - a)
    norm_num at hbinom
    have hsum : ∑ b ∈ Finset.range (L - a + 1), ((L - a).choose b : ℝ) = (2 : ℝ) ^ (L - a) := by
      simpa using hbinom.symm
    calc ∑ b ∈ Finset.range (L - a + 1), T a b (L - a - b)
        = (a.factorial : ℝ)⁻¹ * ((L - a).factorial : ℝ)⁻¹ *
            ∑ b ∈ Finset.range (L - a + 1), ((L - a).choose b : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b hb => ?_
          rw [mem_range] at hb
          have hle : b ≤ L - a := by omega
          have hch := Nat.choose_mul_factorial_mul_factorial hle
          have hchR : ((L - a).choose b : ℝ) * (b.factorial : ℝ) * ((L - a - b).factorial : ℝ) =
              ((L - a).factorial : ℝ) := by exact_mod_cast hch
          unfold T
          have hfa : (a.factorial : ℝ) ≠ 0 := by positivity
          have hfb : (b.factorial : ℝ) ≠ 0 := by positivity
          have hfc : ((L - a - b).factorial : ℝ) ≠ 0 := by positivity
          have hfm : ((L - a).factorial : ℝ) ≠ 0 := by positivity
          field_simp; linarith
      _ = (a.factorial : ℝ)⁻¹ * ((2 : ℝ) ^ (L - a) / ((L - a).factorial : ℝ)) := by
          rw [hsum]; ring
  calc ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L - a + 1), T a b (L - a - b)
      = ∑ a ∈ Finset.range (L + 1),
          (a.factorial : ℝ)⁻¹ * ((2 : ℝ) ^ (L - a) / ((L - a).factorial : ℝ)) := by
        refine Finset.sum_congr rfl fun a ha => hinner a (by rw [mem_range] at ha; omega)
    _ = (L.factorial : ℝ)⁻¹ * ∑ a ∈ Finset.range (L + 1), (L.choose a : ℝ) * (2 : ℝ) ^ (L - a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [mem_range] at ha
        have hle : a ≤ L := by omega
        have hch := Nat.choose_mul_factorial_mul_factorial hle
        have hchR : (L.choose a : ℝ) * (a.factorial : ℝ) * ((L - a).factorial : ℝ) =
            (L.factorial : ℝ) := by exact_mod_cast hch
        have hfa : (a.factorial : ℝ) ≠ 0 := by positivity
        have hfm : ((L - a).factorial : ℝ) ≠ 0 := by positivity
        have hfL : (L.factorial : ℝ) ≠ 0 := by positivity
        field_simp; nlinarith
    _ = (3 : ℝ) ^ L / (L.factorial : ℝ) := by
        have h3 := add_pow (1 : ℝ) (2 : ℝ) L
        have hsum3 : ∑ a ∈ Finset.range (L + 1), (L.choose a : ℝ) * (2 : ℝ) ^ (L - a) = (3 : ℝ) ^ L := by
          have h12 : (1 : ℝ) + 2 = 3 := by norm_num
          rw [h12] at h3
          rw [h3]
          refine Finset.sum_congr rfl fun a _ => by ring
        rw [hsum3]; ring

lemma sum_simplex3_fst_T (L : ℕ) (hL : 1 ≤ L) :
    ∑ t ∈ simplex3 L, (t.1 : ℝ) * T t.1 t.2.1 t.2.2 = (3 : ℝ) ^ (L - 1) / ((L - 1).factorial : ℝ) := by
  rw [← sum_simplex3_T (L - 1)]
  rw [← Finset.sum_filter_add_sum_filter_not (simplex3 L) (fun t => t.1 ≠ 0)]
  have hzero : ∑ t ∈ (simplex3 L).filter (fun t => ¬ t.1 ≠ 0), (t.1 : ℝ) * T t.1 t.2.1 t.2.2 = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [mem_filter] at ht
    have h0 : t.1 = 0 := by omega
    simp [h0]
  rw [hzero, add_zero]
  refine Finset.sum_bij (fun t _ => (t.1 - 1, t.2.1, t.2.2)) ?_ ?_ ?_ ?_
  · intro ⟨a, b, c⟩ ht; rw [mem_filter, mem_simplex3] at ht; rw [mem_simplex3]; dsimp only at ht ⊢; omega
  · intro ⟨a1, b1, c1⟩ ht1 ⟨a2, b2, c2⟩ ht2 h
    rw [mem_filter, mem_simplex3] at ht1 ht2
    simp only [Prod.mk.injEq] at h
    dsimp only at ht1 ht2 h
    obtain ⟨h1, rfl, rfl⟩ := h
    exact Prod.ext (by omega) (Prod.ext rfl rfl)
  · intro ⟨a, b, c⟩ ht
    rw [mem_simplex3] at ht; dsimp only at ht
    refine ⟨(a + 1, b, c), ?_, by simp⟩
    rw [mem_filter, mem_simplex3]; dsimp only; omega
  · intro ⟨a, b, c⟩ ht
    rw [mem_filter] at ht; dsimp only at ht ⊢
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact mul_T_fst a' b c

lemma sum_simplex3_fst_mul_fst_sub_one_T (L : ℕ) (hL : 2 ≤ L) :
    ∑ t ∈ simplex3 L, (t.1 : ℝ) * ((t.1 : ℝ) - 1) * T t.1 t.2.1 t.2.2 =
      (3 : ℝ) ^ (L - 2) / ((L - 2).factorial : ℝ) := by
  rw [← sum_simplex3_T (L - 2)]
  rw [← Finset.sum_filter_add_sum_filter_not (simplex3 L) (fun t => 2 ≤ t.1)]
  have hzero : ∑ t ∈ (simplex3 L).filter (fun t => ¬ 2 ≤ t.1),
      (t.1 : ℝ) * ((t.1 : ℝ) - 1) * T t.1 t.2.1 t.2.2 = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [mem_filter] at ht
    have : t.1 = 0 ∨ t.1 = 1 := by omega
    rcases this with h | h <;> simp [h]
  rw [hzero, add_zero]
  refine Finset.sum_bij (fun t _ => (t.1 - 2, t.2.1, t.2.2)) ?_ ?_ ?_ ?_
  · intro ⟨a, b, c⟩ ht; rw [mem_filter, mem_simplex3] at ht; rw [mem_simplex3]; dsimp only at ht ⊢; omega
  · intro ⟨a1, b1, c1⟩ ht1 ⟨a2, b2, c2⟩ ht2 h
    rw [mem_filter, mem_simplex3] at ht1 ht2
    simp only [Prod.mk.injEq] at h
    dsimp only at ht1 ht2 h
    obtain ⟨h1, rfl, rfl⟩ := h
    exact Prod.ext (by omega) (Prod.ext rfl rfl)
  · intro ⟨a, b, c⟩ ht
    rw [mem_simplex3] at ht; dsimp only at ht
    refine ⟨(a + 2, b, c), ?_, by simp⟩
    rw [mem_filter, mem_simplex3]; dsimp only; omega
  · intro ⟨a, b, c⟩ ht
    rw [mem_filter] at ht; dsimp only at ht ⊢
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
    rw [Nat.add_sub_cancel]
    calc ((a' + 2 : ℕ) : ℝ) * (((a' + 2 : ℕ) : ℝ) - 1) * T (a' + 2) b c
        = ((a' + 1 : ℕ) : ℝ) * (((a' + 1 + 1 : ℕ) : ℝ) * T (a' + 1 + 1) b c) := by push_cast; ring
      _ = ((a' + 1 : ℕ) : ℝ) * T (a' + 1) b c := by rw [mul_T_fst (a' + 1) b c]
      _ = T a' b c := mul_T_fst a' b c

lemma sum_simplex3_fst_mul_snd_T (L : ℕ) (hL : 2 ≤ L) :
    ∑ t ∈ simplex3 L, (t.1 : ℝ) * (t.2.1 : ℝ) * T t.1 t.2.1 t.2.2 =
      (3 : ℝ) ^ (L - 2) / ((L - 2).factorial : ℝ) := by
  rw [← sum_simplex3_T (L - 2)]
  rw [← Finset.sum_filter_add_sum_filter_not (simplex3 L) (fun t => 1 ≤ t.1 ∧ 1 ≤ t.2.1)]
  have hzero : ∑ t ∈ (simplex3 L).filter (fun t => ¬ (1 ≤ t.1 ∧ 1 ≤ t.2.1)),
      (t.1 : ℝ) * (t.2.1 : ℝ) * T t.1 t.2.1 t.2.2 = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [mem_filter] at ht
    have : t.1 = 0 ∨ t.2.1 = 0 := by omega
    rcases this with h | h <;> simp [h]
  rw [hzero, add_zero]
  refine Finset.sum_bij (fun t _ => (t.1 - 1, t.2.1 - 1, t.2.2)) ?_ ?_ ?_ ?_
  · intro ⟨a, b, c⟩ ht; rw [mem_filter, mem_simplex3] at ht; rw [mem_simplex3]; dsimp only at ht ⊢; omega
  · intro ⟨a1, b1, c1⟩ ht1 ⟨a2, b2, c2⟩ ht2 h
    rw [mem_filter, mem_simplex3_mk] at ht1 ht2
    simp only [Prod.mk.injEq] at h
    rcases ht1 with ⟨ht1s, ht1a, ht1b⟩
    rcases ht2 with ⟨ht2s, ht2a, ht2b⟩
    obtain ⟨h1, h2, rfl⟩ := h
    change 1 ≤ a1 at ht1a; change 1 ≤ b1 at ht1b
    change 1 ≤ a2 at ht2a; change 1 ≤ b2 at ht2b
    simp only [Prod.mk.injEq]; exact ⟨by omega, by omega, trivial⟩
  · intro ⟨a, b, c⟩ ht
    rw [mem_simplex3] at ht; dsimp only at ht
    refine ⟨(a + 1, b + 1, c), ?_, by simp⟩
    rw [mem_filter, mem_simplex3]; dsimp only; omega
  · intro ⟨a, b, c⟩ ht
    rw [mem_filter] at ht; dsimp only at ht ⊢
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel, mul_assoc, mul_T_snd, mul_T_fst]

lemma sum_simplex3_cyc (L : ℕ) (f : ℕ × ℕ × ℕ → ℝ) :
    ∑ t ∈ simplex3 L, f (t.2.1, t.2.2, t.1) = ∑ t ∈ simplex3 L, f t := by
  refine Finset.sum_bij (fun t _ => (t.2.1, t.2.2, t.1)) ?_ ?_ ?_ ?_
  · intro ⟨a, b, c⟩ ht; rw [mem_simplex3] at ht ⊢; dsimp only at ht ⊢; omega
  · intro ⟨a1, b1, c1⟩ _ ⟨a2, b2, c2⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2.2 (Prod.ext h.1 h.2.1)
  · intro ⟨a, b, c⟩ ht; rw [mem_simplex3] at ht; dsimp only at ht
    exact ⟨(c, a, b), mem_simplex3.mpr (by dsimp only; omega), rfl⟩
  · intro _ _; rfl

lemma sum_simplex3_cyc2 (L : ℕ) (f : ℕ × ℕ × ℕ → ℝ) :
    ∑ t ∈ simplex3 L, f (t.2.2, t.1, t.2.1) = ∑ t ∈ simplex3 L, f t := by
  have h1 := sum_simplex3_cyc L (fun t => f (t.2.1, t.2.2, t.1))
  have h2 := sum_simplex3_cyc L f
  exact h1.trans h2

lemma sum_simplex3_swap12 (L : ℕ) (f : ℕ × ℕ × ℕ → ℝ) :
    ∑ t ∈ simplex3 L, f (t.2.1, t.1, t.2.2) = ∑ t ∈ simplex3 L, f t := by
  refine Finset.sum_bij (fun t _ => (t.2.1, t.1, t.2.2)) ?_ ?_ ?_ ?_
  · intro ⟨a, b, c⟩ ht; rw [mem_simplex3] at ht ⊢; dsimp only at ht ⊢; omega
  · intro ⟨a1, b1, c1⟩ _ ⟨a2, b2, c2⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)
  · intro ⟨a, b, c⟩ ht; rw [mem_simplex3] at ht; dsimp only at ht
    exact ⟨(b, a, c), mem_simplex3.mpr (by dsimp only; omega), rfl⟩
  · intro _ _; rfl

lemma sum_simplex3_swap23 (L : ℕ) (f : ℕ × ℕ × ℕ → ℝ) :
    ∑ t ∈ simplex3 L, f (t.1, t.2.2, t.2.1) = ∑ t ∈ simplex3 L, f t := by
  have h1 := sum_simplex3_cyc L (fun t => f (t.2.2, t.2.1, t.1))
  have h2 := sum_simplex3_swap12 L (fun t => f (t.2.2, t.1, t.2.1))
  have h3 := sum_simplex3_cyc2 L f
  exact (h1.trans h2).trans h3

lemma sum_simplex3_swap13 (L : ℕ) (f : ℕ × ℕ × ℕ → ℝ) :
    ∑ t ∈ simplex3 L, f (t.2.2, t.2.1, t.1) = ∑ t ∈ simplex3 L, f t := by
  have h1 := sum_simplex3_swap12 L (fun t => f (t.2.2, t.1, t.2.1))
  have h2 := sum_simplex3_cyc2 L f
  exact h1.trans h2

lemma sum_simplex3_sq_diff (L : ℕ) (hL : 2 ≤ L) :
    ∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 * ((t.1 : ℝ) - (t.2.1 : ℝ)) ^ 2 =
      2 * (3 : ℝ) ^ (L - 1) / ((L - 1).factorial : ℝ) := by
  have hsq : ∀ t : ℕ × ℕ × ℕ,
      T t.1 t.2.1 t.2.2 * ((t.1 : ℝ) - (t.2.1 : ℝ)) ^ 2 =
        (t.1 : ℝ) * ((t.1 : ℝ) - 1) * T t.1 t.2.1 t.2.2 + (t.1 : ℝ) * T t.1 t.2.1 t.2.2 +
        ((t.2.1 : ℝ) * ((t.2.1 : ℝ) - 1) * T t.1 t.2.1 t.2.2 + (t.2.1 : ℝ) * T t.1 t.2.1 t.2.2) -
        2 * ((t.1 : ℝ) * (t.2.1 : ℝ) * T t.1 t.2.1 t.2.2) := by
    intro t; ring
  simp_rw [hsq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hs1 := sum_simplex3_fst_mul_fst_sub_one_T L hL
  have hs2 := sum_simplex3_fst_T L (by omega)
  have hs3 := sum_simplex3_fst_mul_snd_T L hL
  have hs1' : ∑ t ∈ simplex3 L, (t.2.1 : ℝ) * ((t.2.1 : ℝ) - 1) * T t.1 t.2.1 t.2.2 =
      (3 : ℝ) ^ (L - 2) / ((L - 2).factorial : ℝ) := by
    rw [← hs1]
    have hsw := sum_simplex3_swap12 L (fun t => (t.1 : ℝ) * ((t.1 : ℝ) - 1) * T t.1 t.2.1 t.2.2)
    simpa [T_symm_12] using hsw
  have hs2' : ∑ t ∈ simplex3 L, (t.2.1 : ℝ) * T t.1 t.2.1 t.2.2 =
      (3 : ℝ) ^ (L - 1) / ((L - 1).factorial : ℝ) := by
    rw [← hs2]
    have hsw := sum_simplex3_swap12 L (fun t => (t.1 : ℝ) * T t.1 t.2.1 t.2.2)
    simpa [T_symm_12] using hsw
  rw [hs1, hs2, hs1', hs2', hs3]
  ring

/-! ### Part 2: Symmetrization of `hAdj L` onto the strictly ordered wedge `a < b < c` -/

private lemma ordered_cyc_abs_identity {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    |b - a| * |c - b| + |c - b| * |a - c| + |a - c| * |b - a| =
      (1 / 2 : ℝ) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) +
      2 * ((if a < b ∧ b < c then (b - a) * (c - b) else 0) +
           (if a < c ∧ c < b then (c - a) * (b - c) else 0) +
           (if b < a ∧ a < c then (a - b) * (c - a) else 0) +
           (if b < c ∧ c < a then (c - b) * (a - c) else 0) +
           (if c < a ∧ a < b then (a - c) * (b - a) else 0) +
           (if c < b ∧ b < a then (b - c) * (a - b) else 0)) := by
  have h1 : |b - a| = b - a := abs_of_nonneg (by linarith)
  have h2 : |c - b| = c - b := abs_of_nonneg (by linarith)
  have h3 : |a - c| = c - a := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
  have hf2 : ¬ (a < c ∧ c < b) := by intro h; linarith
  have hf3 : ¬ (b < a ∧ a < c) := by intro h; linarith
  have hf4 : ¬ (b < c ∧ c < a) := by intro h; linarith
  have hf5 : ¬ (c < a ∧ a < b) := by intro h; linarith
  have hf6 : ¬ (c < b ∧ b < a) := by intro h; linarith
  have hterm1 : (if a < b ∧ b < c then (b - a) * (c - b) else 0) = (b - a) * (c - b) := by
    by_cases h : a < b ∧ b < c
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      have : a = b ∨ b = c := by
        by_contra hne; push Not at hne
        exact h ⟨lt_of_le_of_ne hab hne.1, lt_of_le_of_ne hbc hne.2⟩
      rcases this with rfl | rfl <;> ring
  rw [h1, h2, h3, hterm1, ite_eq_right hf2, ite_eq_right hf3,
      ite_eq_right hf4, ite_eq_right hf5, ite_eq_right hf6]
  ring

lemma pointwise_cyc_abs_identity (x1 x2 x3 : ℝ) :
    |x2 - x1| * |x3 - x2| + |x3 - x2| * |x1 - x3| + |x1 - x3| * |x2 - x1| =
      (1 / 2 : ℝ) * ((x1 - x2) ^ 2 + (x2 - x3) ^ 2 + (x3 - x1) ^ 2) +
      2 * ((if x1 < x2 ∧ x2 < x3 then (x2 - x1) * (x3 - x2) else 0) +
           (if x1 < x3 ∧ x3 < x2 then (x3 - x1) * (x2 - x3) else 0) +
           (if x2 < x1 ∧ x1 < x3 then (x1 - x2) * (x3 - x1) else 0) +
           (if x2 < x3 ∧ x3 < x1 then (x3 - x2) * (x1 - x3) else 0) +
           (if x3 < x1 ∧ x1 < x2 then (x1 - x3) * (x2 - x1) else 0) +
           (if x3 < x2 ∧ x2 < x1 then (x2 - x3) * (x1 - x2) else 0)) := by
  have h12 : |x1 - x2| = |x2 - x1| := abs_sub_comm x1 x2
  have h23 : |x2 - x3| = |x3 - x2| := abs_sub_comm x2 x3
  have h31 : |x3 - x1| = |x1 - x3| := abs_sub_comm x3 x1
  rcases le_total x1 x2 with h1 | h1 <;>
  rcases le_total x2 x3 with h2 | h2 <;>
  rcases le_total x1 x3 with h3 | h3
  · exact ordered_cyc_abs_identity h1 h2
  · exact ordered_cyc_abs_identity h1 h2
  · have he := ordered_cyc_abs_identity h3 h2; rw [h12, h23, h31] at *; linear_combination he
  · have he := ordered_cyc_abs_identity h3 h1; rw [h12, h23, h31] at *; linear_combination he
  · have he := ordered_cyc_abs_identity h1 h3; rw [h12, h23, h31] at *; linear_combination he
  · have he := ordered_cyc_abs_identity h2 h3; rw [h12, h23, h31] at *; linear_combination he
  · have he := ordered_cyc_abs_identity h2 h1; rw [h12, h23, h31] at *; linear_combination he
  · have he := ordered_cyc_abs_identity h2 h1; rw [h12, h23, h31] at *; linear_combination he

/-- The strictly ordered wedge sum `uvSum L = ∑_{a < b < c, a+b+c = L} (b - a)(c - b) / (a! b! c!)`. -/
noncomputable def uvSum (L : ℕ) : ℝ :=
  ∑ t ∈ (simplex3 L).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2),
    ((t.2.1 : ℝ) - (t.1 : ℝ)) * ((t.2.2 : ℝ) - (t.2.1 : ℝ)) * T t.1 t.2.1 t.2.2

lemma hAdj_eq_uvSum (L : ℕ) (hL : 2 ≤ L) :
    hAdj L = (L : ℝ) / 3 + 4 * ((L.factorial : ℝ) / (3 : ℝ) ^ L) * uvSum L := by
  unfold hAdj
  have hcyc1 : ∑ t ∈ simplex3 L, ((L.factorial : ℝ) * T t.1 t.2.1 t.2.2) *
      |(t.2.1 : ℝ) - (t.1 : ℝ)| * |(t.2.2 : ℝ) - (t.2.1 : ℝ)| =
      (L.factorial : ℝ) * ∑ t ∈ simplex3 L,
        T t.1 t.2.1 t.2.2 * (|(t.2.1 : ℝ) - (t.1 : ℝ)| * |(t.2.2 : ℝ) - (t.2.1 : ℝ)|) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => by ring
  rw [hcyc1]
  have h3cyc : 3 * ∑ t ∈ simplex3 L,
      T t.1 t.2.1 t.2.2 * (|(t.2.1 : ℝ) - (t.1 : ℝ)| * |(t.2.2 : ℝ) - (t.2.1 : ℝ)|) =
      ∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 *
        (|(t.2.1 : ℝ) - (t.1 : ℝ)| * |(t.2.2 : ℝ) - (t.2.1 : ℝ)| +
         |(t.2.2 : ℝ) - (t.2.1 : ℝ)| * |(t.1 : ℝ) - (t.2.2 : ℝ)| +
         |(t.1 : ℝ) - (t.2.2 : ℝ)| * |(t.2.1 : ℝ) - (t.1 : ℝ)|) := by
    have hsplit : ∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 *
        (|(t.2.1 : ℝ) - (t.1 : ℝ)| * |(t.2.2 : ℝ) - (t.2.1 : ℝ)| +
         |(t.2.2 : ℝ) - (t.2.1 : ℝ)| * |(t.1 : ℝ) - (t.2.2 : ℝ)| +
         |(t.1 : ℝ) - (t.2.2 : ℝ)| * |(t.2.1 : ℝ) - (t.1 : ℝ)|) =
      (∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 * (|(t.2.1 : ℝ) - (t.1 : ℝ)| * |(t.2.2 : ℝ) - (t.2.1 : ℝ)|)) +
      (∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 * (|(t.2.2 : ℝ) - (t.2.1 : ℝ)| * |(t.1 : ℝ) - (t.2.2 : ℝ)|)) +
      (∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 * (|(t.1 : ℝ) - (t.2.2 : ℝ)| * |(t.2.1 : ℝ) - (t.1 : ℝ)|)) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    rw [hsplit]
    have h2 : ∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 * (|(t.2.2 : ℝ) - (t.2.1 : ℝ)| * |(t.1 : ℝ) - (t.2.2 : ℝ)|) =
        ∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 * (|(t.2.1 : ℝ) - (t.1 : ℝ)| * |(t.2.2 : ℝ) - (t.2.1 : ℝ)|) := by
      simpa [← T_symm_cyc] using sum_simplex3_cyc L (fun t =>
        T t.1 t.2.1 t.2.2 * (|(t.2.1 : ℝ) - (t.1 : ℝ)| * |(t.2.2 : ℝ) - (t.2.1 : ℝ)|))
    have h3 : ∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 * (|(t.1 : ℝ) - (t.2.2 : ℝ)| * |(t.2.1 : ℝ) - (t.1 : ℝ)|) =
        ∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 * (|(t.2.2 : ℝ) - (t.2.1 : ℝ)| * |(t.1 : ℝ) - (t.2.2 : ℝ)|) := by
      simpa [← T_symm_cyc] using sum_simplex3_cyc L (fun t =>
        T t.1 t.2.1 t.2.2 * (|(t.2.2 : ℝ) - (t.2.1 : ℝ)| * |(t.1 : ℝ) - (t.2.2 : ℝ)|))
    linarith
  let gOrd : ℕ × ℕ × ℕ → ℝ := fun t =>
    T t.1 t.2.1 t.2.2 * (if (t.1 : ℝ) < t.2.1 ∧ (t.2.1 : ℝ) < t.2.2
      then ((t.2.1 : ℝ) - t.1) * ((t.2.2 : ℝ) - t.2.1) else 0)
  have hgOrd : ∑ t ∈ simplex3 L, gOrd t = uvSum L := by
    unfold uvSum
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    dsimp only [gOrd]
    have hiff : ((t.1 : ℝ) < t.2.1 ∧ (t.2.1 : ℝ) < t.2.2) ↔ (t.1 < t.2.1 ∧ t.2.1 < t.2.2) := by
      exact_mod_cast Iff.rfl
    simp only [hiff]
    split_ifs <;> ring
  have hrhs : ∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 *
      (|(t.2.1 : ℝ) - (t.1 : ℝ)| * |(t.2.2 : ℝ) - (t.2.1 : ℝ)| +
       |(t.2.2 : ℝ) - (t.2.1 : ℝ)| * |(t.1 : ℝ) - (t.2.2 : ℝ)| +
       |(t.1 : ℝ) - (t.2.2 : ℝ)| * |(t.2.1 : ℝ) - (t.1 : ℝ)|) =
      3 * ((3 : ℝ) ^ (L - 1) / ((L - 1).factorial : ℝ)) + 12 * uvSum L := by
    have hpt : ∀ t ∈ simplex3 L,
        T t.1 t.2.1 t.2.2 *
        (|(t.2.1 : ℝ) - (t.1 : ℝ)| * |(t.2.2 : ℝ) - (t.2.1 : ℝ)| +
         |(t.2.2 : ℝ) - (t.2.1 : ℝ)| * |(t.1 : ℝ) - (t.2.2 : ℝ)| +
         |(t.1 : ℝ) - (t.2.2 : ℝ)| * |(t.2.1 : ℝ) - (t.1 : ℝ)|) =
        (1 / 2 : ℝ) * (T t.1 t.2.1 t.2.2 * ((t.1 : ℝ) - (t.2.1 : ℝ)) ^ 2 +
                       T t.1 t.2.1 t.2.2 * ((t.2.1 : ℝ) - (t.2.2 : ℝ)) ^ 2 +
                       T t.1 t.2.1 t.2.2 * ((t.2.2 : ℝ) - (t.1 : ℝ)) ^ 2) +
        2 * (gOrd (t.1, t.2.1, t.2.2) + gOrd (t.1, t.2.2, t.2.1) + gOrd (t.2.1, t.1, t.2.2) +
             gOrd (t.2.1, t.2.2, t.1) + gOrd (t.2.2, t.1, t.2.1) + gOrd (t.2.2, t.2.1, t.1)) := by
      intro t _
      dsimp only [gOrd]
      rw [T_symm_23 t.1 t.2.2 t.2.1, T_symm_12 t.2.1 t.1 t.2.2,
          ← T_symm_cyc t.1 t.2.1 t.2.2, T_symm_cyc t.2.2 t.1 t.2.1, T_symm_13 t.2.2 t.2.1 t.1]
      rw [pointwise_cyc_abs_identity (t.1 : ℝ) (t.2.1 : ℝ) (t.2.2 : ℝ)]
      ring
    rw [Finset.sum_congr rfl hpt]
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    have hsq1 := sum_simplex3_sq_diff L hL
    have hsq2 : ∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 * ((t.2.1 : ℝ) - (t.2.2 : ℝ)) ^ 2 =
        2 * (3 : ℝ) ^ (L - 1) / ((L - 1).factorial : ℝ) := by
      rw [← hsq1]
      simpa [← T_symm_cyc] using sum_simplex3_cyc L (fun t => T t.1 t.2.1 t.2.2 * ((t.1 : ℝ) - (t.2.1 : ℝ)) ^ 2)
    have hsq3 : ∑ t ∈ simplex3 L, T t.1 t.2.1 t.2.2 * ((t.2.2 : ℝ) - (t.1 : ℝ)) ^ 2 =
        2 * (3 : ℝ) ^ (L - 1) / ((L - 1).factorial : ℝ) := by
      rw [← hsq2]
      simpa [← T_symm_cyc] using sum_simplex3_cyc L (fun t => T t.1 t.2.1 t.2.2 * ((t.2.1 : ℝ) - (t.2.2 : ℝ)) ^ 2)
    rw [sum_simplex3_swap23 L gOrd, sum_simplex3_swap12 L gOrd, sum_simplex3_cyc L gOrd,
        sum_simplex3_cyc2 L gOrd, sum_simplex3_swap13 L gOrd, hgOrd, hsq1, hsq2, hsq3]
    ring
  have hmain : ∑ t ∈ simplex3 L,
      T t.1 t.2.1 t.2.2 * (|(t.2.1 : ℝ) - (t.1 : ℝ)| * |(t.2.2 : ℝ) - (t.2.1 : ℝ)|) =
      (3 : ℝ) ^ (L - 1) / ((L - 1).factorial : ℝ) + 4 * uvSum L := by
    linarith
  rw [hmain]
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.factorial_succ, pow_succ, inv_pow]
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  have h3 : (3 : ℝ) ^ m ≠ 0 := by positivity
  push_cast; field_simp; ring

/-! ### Part 3: Two-step exact 1D telescoping of `uvSum L` -/

lemma inner_telescope (a M : ℕ) (hB : a + 1 ≤ (M - 1) / 2) :
    ∑ b ∈ Finset.Icc (a + 1) ((M - 1) / 2),
      ((b : ℝ) - (a : ℝ)) * (((M - b : ℕ) : ℝ) - (b : ℝ)) * T a b (M - b) =
    ((((M - 1) / 2 : ℕ) : ℝ) - (a : ℝ)) * T a ((M - 1) / 2) (M - (M - 1) / 2 - 1) -
    ∑ b ∈ Finset.Icc (a + 1) ((M - 1) / 2), T a (b - 1) (M - b) := by
  set B := (M - 1) / 2
  have hstep : ∀ b ∈ Finset.Icc (a + 1) B,
      ((b : ℝ) - (a : ℝ)) * (((M - b : ℕ) : ℝ) - (b : ℝ)) * T a b (M - b) =
        (((b : ℝ) - (a : ℝ)) * T a b (M - b - 1) - (((b - 1 : ℕ) : ℝ) - (a : ℝ)) * T a (b - 1) (M - b)) -
        T a (b - 1) (M - b) := by
    intro b hb
    rw [mem_Icc] at hb
    obtain ⟨b', hb'⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    obtain ⟨c', hc'⟩ : ∃ c', M - b = c' + 1 := ⟨M - b - 1, by omega⟩
    have hMb1 : M - b - 1 = c' := by omega
    have hbm1 : b - 1 = b' := by omega
    have h1 : (((M - b : ℕ) : ℝ)) * T a b (M - b) = T a b c' := by
      rw [hc']; exact mul_T_thd a b c'
    have h2 : (b : ℝ) * T a b (M - b) = T a b' (M - b) := by
      set c := M - b
      rw [hb']; exact mul_T_snd a b' c
    rw [hMb1, hbm1]
    have hcast : ((b' : ℝ) - (a : ℝ)) = ((b : ℝ) - (a : ℝ)) - 1 := by
      rw [hb']; push_cast; ring
    rw [hcast]
    calc ((b : ℝ) - (a : ℝ)) * (((M - b : ℕ) : ℝ) - (b : ℝ)) * T a b (M - b)
        = ((b : ℝ) - (a : ℝ)) * ((((M - b : ℕ) : ℝ) * T a b (M - b)) - ((b : ℝ) * T a b (M - b))) := by ring
      _ = ((b : ℝ) - (a : ℝ)) * (T a b c' - T a b' (M - b)) := by rw [h1, h2]
      _ = (((b : ℝ) - (a : ℝ)) * T a b c' - (((b : ℝ) - (a : ℝ)) - 1) * T a b' (M - b)) -
            T a b' (M - b) := by ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib]
  congr 1
  let ψ : ℕ → ℝ := fun b => ((b : ℝ) - (a : ℝ)) * T a b (M - b - 1)
  have htel : ∑ b ∈ Finset.Icc (a + 1) B,
      (((b : ℝ) - (a : ℝ)) * T a b (M - b - 1) - (((b - 1 : ℕ) : ℝ) - (a : ℝ)) * T a (b - 1) (M - b)) =
      ∑ k ∈ Finset.range (B - a), (ψ (a + (k + 1)) - ψ (a + k)) := by
    refine Finset.sum_bij (fun b _ => b - (a + 1)) ?_ ?_ ?_ ?_
    · intro b hb; rw [mem_Icc] at hb; rw [mem_range]; omega
    · intro b1 hb1 b2 hb2 h; rw [mem_Icc] at hb1 hb2; omega
    · intro k hk; rw [mem_range] at hk
      exact ⟨a + k + 1, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro b hb
      rw [mem_Icc] at hb
      have h1 : a + (b - (a + 1) + 1) = b := by omega
      have h2 : a + (b - (a + 1)) = b - 1 := by omega
      have h3 : M - (b - 1) - 1 = M - b := by omega
      simp only [ψ, h1, h2, h3]
  rw [htel, Finset.sum_range_sub (fun k => ψ (a + k)) (B - a)]
  have hBa : a + (B - a) = B := by omega
  simp only [ψ, hBa, add_zero, sub_self, zero_mul, sub_zero]

/-- The shifted telescoping potential `Φ_L(a + 1)` with `Φ_L(0) = 0`. -/
noncomputable def PhiNat (L : ℕ) : ℕ → ℝ
  | 0 => 0
  | a + 1 =>
    if (L - a) % 2 = 0 then T a ((L - a) / 2 - 2) ((L - a) / 2)
    else T a ((L - a - 1) / 2 - 1) ((L - a - 1) / 2)

/-- Boundary term of the inner telescope at index `a`. -/
noncomputable def bdryTerm (L a : ℕ) : ℝ :=
  if 3 * a + 3 ≤ L then
    ((((L - a - 1) / 2 : ℕ) : ℝ) - (a : ℝ)) *
      T a ((L - a - 1) / 2) (L - a - (L - a - 1) / 2 - 1)
  else 0

/-- Extra odd-parity term `T(a - 1, k, k + 1)` when `L - a = 2k + 1` and `a ≥ 1`. -/
noncomputable def extraOddTerm (L a : ℕ) : ℝ :=
  if (L - a) % 2 = 1 ∧ 1 ≤ a then
    T (a - 1) ((L - a - 1) / 2) ((L - a - 1) / 2 + 1)
  else 0

/-- One-line exact telescoping identity: for `3 ≤ L` and `a ≤ (L - 1) / 3`,
`bdryTerm L a + extraOddTerm L a = PhiNat L (a + 1) - PhiNat L a`. -/
lemma bdry_add_extra_eq_PhiNat_sub (L a : ℕ) (hL : 3 ≤ L) (ha : a ≤ (L - 1) / 3) :
    bdryTerm L a + extraOddTerm L a = PhiNat L (a + 1) - PhiNat L a := by
  have h3a : 3 * a ≤ L - 1 := by omega
  have hM : 3 ≤ L - a := by omega
  set k := (L - a) / 2
  rcases Nat.mod_two_eq_zero_or_one (L - a) with hmod | hmod
  · -- Case 1: L - a = 2 * k (even), k ≥ 2
    have hk : L - a = 2 * k := by omega
    have hk2 : 2 ≤ k := by omega
    have hdiv : (L - a) / 2 = k := rfl
    have hB : (L - a - 1) / 2 = k - 1 := by omega
    have hMB1 : L - a - (L - a - 1) / 2 - 1 = k := by omega
    have hex : extraOddTerm L a = 0 := by
      unfold extraOddTerm; rw [ite_eq_right (by omega)]
    rw [hex, add_zero]
    have hPhi_succ : PhiNat L (a + 1) = T a (k - 2) k := by
      simp only [PhiNat, hmod, ↓reduceIte, hdiv]
    rw [hPhi_succ]
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · simp only [PhiNat, sub_zero]
      unfold bdryTerm
      rw [ite_eq_left (by omega), hMB1, hB]
      obtain ⟨k', hk'⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      have hkm1 : k - 1 = k' + 1 := by omega
      have hkm2 : k - 2 = k' := by omega
      rw [hkm1, hkm2]
      simp only [Nat.cast_zero, sub_zero]
      exact mul_T_snd 0 k' k
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      have hmod_prev : (L - a') % 2 = 1 := by omega
      have hdiv_prev : (L - a' - 1) / 2 = k := by omega
      have hPhi_prev : PhiNat L (a' + 1) = T a' (k - 1) k := by
        simp only [PhiNat, hmod_prev, one_ne_zero, ↓reduceIte, hdiv_prev]
      rw [hPhi_prev]
      have hval : bdryTerm L (a' + 1) =
          (((k - 1 : ℕ) : ℝ) - ((a' + 1 : ℕ) : ℝ)) * T (a' + 1) (k - 1) k := by
        unfold bdryTerm
        split_ifs with hcond
        · rw [hMB1, hB]
        · have heq : k - 1 = a' + 1 := by omega
          rw [heq, sub_self, zero_mul]
      rw [hval]
      obtain ⟨k', hk'⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      have hkm1 : k - 1 = k' + 1 := by omega
      have hkm2 : k - 2 = k' := by omega
      rw [hkm1, hkm2, sub_mul, mul_T_snd (a' + 1) k' k, mul_T_fst a' (k' + 1) k]
  · -- Case 2: L - a = 2 * k + 1 (odd), k ≥ 1
    have hk : L - a = 2 * k + 1 := by omega
    have hk1 : 1 ≤ k := by omega
    have hB : (L - a - 1) / 2 = k := by omega
    have hMB1 : L - a - (L - a - 1) / 2 - 1 = k := by omega
    have hPhi_succ : PhiNat L (a + 1) = T a (k - 1) k := by
      simp only [PhiNat, hmod, one_ne_zero, ↓reduceIte, hB]
    rw [hPhi_succ]
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · simp only [PhiNat, sub_zero]
      have hex : extraOddTerm L 0 = 0 := by
        unfold extraOddTerm; rw [ite_eq_right (by omega)]
      rw [hex, add_zero]
      unfold bdryTerm
      rw [ite_eq_left (by omega), hMB1, hB]
      obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hkm1 : k - 1 = k' := by omega
      rw [hkm1]
      simp only [Nat.cast_zero, sub_zero]
      rw [hk']
      exact mul_T_snd 0 k' (k' + 1)
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      have hmod_prev : (L - a') % 2 = 0 := by omega
      have hdiv_prev : (L - a') / 2 = k + 1 := by omega
      have hPhi_prev : PhiNat L (a' + 1) = T a' (k - 1) (k + 1) := by
        simp only [PhiNat, hmod_prev, ↓reduceIte, hdiv_prev]
        have : k + 1 - 2 = k - 1 := by omega
        rw [this]
      rw [hPhi_prev]
      have hex : extraOddTerm L (a' + 1) = T a' k (k + 1) := by
        unfold extraOddTerm
        rw [ite_eq_left (by omega), hB, Nat.add_sub_cancel]
      rw [hex]
      have hval : bdryTerm L (a' + 1) =
          ((k : ℝ) - ((a' + 1 : ℕ) : ℝ)) * T (a' + 1) k k := by
        unfold bdryTerm
        split_ifs with hcond
        · rw [hMB1, hB]
        · have heq : k = a' + 1 := by omega
          rw [heq, sub_self, zero_mul]
      rw [hval]
      obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hkm1 : k - 1 = k' := by omega
      rw [hkm1, sub_mul]
      have h1 : (k : ℝ) * T (a' + 1) k k = T (a' + 1) k' k := by
        rw [hk']; exact mul_T_snd (a' + 1) k' (k' + 1)
      have h2 : ((a' + 1 : ℕ) : ℝ) * T (a' + 1) k k = T a' k k := mul_T_fst a' k k
      have h3 : T a' k (k + 1) = T a' k k - T a' k' (k + 1) := by
        have ha1 := mul_T_thd a' k k
        have ha2 : (k : ℝ) * T a' k (k + 1) = T a' k' (k + 1) := by
          rw [hk']; exact mul_T_snd a' k' (k' + 1 + 1)
        have hdiff : ((k + 1 : ℕ) : ℝ) * T a' k (k + 1) - (k : ℝ) * T a' k (k + 1) = T a' k (k + 1) := by
          push_cast; ring
        linarith
      rw [h1, h2, h3]; ring

/-- Bulk sum `bulkSum L = ∑_{a < b < c, a+b+c = L} T(a, b - 1, c)`. -/
noncomputable def bulkSum (L : ℕ) : ℝ :=
  ∑ t ∈ (simplex3 L).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2),
    T t.1 (t.2.1 - 1) t.2.2

/-- Exact Step 1 identity: `uvSum L = ∑_{a=0}^{(L-1)/3} bdryTerm L a - bulkSum L`. -/
lemma uvSum_eq_bdry_sub_bulk (L : ℕ) (hL : 3 ≤ L) :
    uvSum L = (∑ a ∈ Finset.range ((L - 1) / 3 + 1), bdryTerm L a) - bulkSum L := by
  have hnest : ∀ (g : ℕ × ℕ × ℕ → ℝ),
      ∑ t ∈ (simplex3 L).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2), g t =
      ∑ a ∈ Finset.range ((L - 1) / 3 + 1),
        ∑ b ∈ Finset.Icc (a + 1) ((L - a - 1) / 2), g (a, b, L - a - b) := by
    intro g
    rw [Finset.sum_sigma']
    refine Finset.sum_bij (fun t _ => ⟨t.1, t.2.1⟩) ?_ ?_ ?_ ?_
    · intro ⟨a, b, c⟩ ht
      rw [mem_filter, mem_simplex3] at ht
      simp only [mem_sigma, mem_range, mem_Icc] at ht ⊢; omega
    · intro ⟨a1, b1, c1⟩ ht1 ⟨a2, b2, c2⟩ ht2 h
      rw [mem_filter, mem_simplex3_mk] at ht1 ht2
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Prod.mk.injEq]; exact ⟨trivial, trivial, by omega⟩
    · intro ⟨a, b⟩ h
      simp only [mem_sigma, mem_range, mem_Icc] at h
      refine ⟨(a, b, L - a - b), ?_, rfl⟩
      rw [mem_filter, mem_simplex3]; dsimp only; omega
    · intro ⟨a, b, c⟩ ht
      rw [mem_filter, mem_simplex3] at ht; dsimp only at ht ⊢
      have hc : L - a - b = c := by omega
      rw [hc]
  unfold uvSum bulkSum
  rw [hnest, hnest, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [mem_range] at ha
  by_cases hcond : 3 * a + 3 ≤ L
  · have hB : a + 1 ≤ (L - a - 1) / 2 := by omega
    have hinner := inner_telescope a (L - a) hB
    have hbdry : bdryTerm L a =
        ((((L - a - 1) / 2 : ℕ) : ℝ) - (a : ℝ)) *
          T a ((L - a - 1) / 2) (L - a - (L - a - 1) / 2 - 1) := by
      unfold bdryTerm; rw [ite_eq_left hcond]
    rw [hbdry, ← hinner]
  · have hIcc : Finset.Icc (a + 1) ((L - a - 1) / 2) = ∅ := by
      rw [Finset.Icc_eq_empty_iff]; omega
    have hbdry : bdryTerm L a = 0 := by
      unfold bdryTerm; rw [ite_eq_right hcond]
    simp [hIcc, hbdry]

private noncomputable def ordWeight (t : ℕ × ℕ × ℕ) : ℝ :=
  if t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 then
    (if t.1 < t.2.1 ∧ t.2.1 < t.2.2 then (1 : ℝ)
     else if t.1 = t.2.1 ∧ t.2.1 = t.2.2 then (1 / 6 : ℝ)
     else (1 / 2 : ℝ)) * T t.1 t.2.1 t.2.2
  else 0

private lemma ordWeight_symm_ordered {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    T a b c =
      ordWeight (a, b, c) + ordWeight (a, c, b) + ordWeight (b, a, c) +
      ordWeight (b, c, a) + ordWeight (c, a, b) + ordWeight (c, b, a) := by
  unfold ordWeight
  dsimp only
  rw [T_symm_23 a c b, T_symm_12 b a c, ← T_symm_cyc a b c, T_symm_cyc c a b, T_symm_13 c b a]
  rcases eq_or_lt_of_le hab with rfl | hab <;> rcases eq_or_lt_of_le hbc with rfl | hbc
  · simp; ring
  · have hf1 : ¬ (a < a ∧ a < c) := by omega
    have hf2 : ¬ (a = a ∧ a = c) := by omega
    have hf3 : ¬ (a ≤ c ∧ c ≤ a) := by omega
    have hf4 : ¬ (c ≤ a ∧ a ≤ a) := by omega
    rw [ite_eq_left ⟨le_rfl, le_of_lt hbc⟩, ite_eq_right hf1, ite_eq_right hf2,
        ite_eq_right hf3, ite_eq_right hf4]
    ring
  · have hf1 : ¬ (a < b ∧ b < b) := by omega
    have hf2 : ¬ (a = b ∧ b = b) := by omega
    have hf3 : ¬ (b ≤ a ∧ a ≤ b) := by omega
    have hf4 : ¬ (b ≤ b ∧ b ≤ a) := by omega
    rw [ite_eq_left ⟨le_of_lt hab, le_rfl⟩, ite_eq_right hf1, ite_eq_right hf2,
        ite_eq_right hf3, ite_eq_right hf4]
    ring
  · have hf2 : ¬ (a ≤ c ∧ c ≤ b) := by omega
    have hf3 : ¬ (b ≤ a ∧ a ≤ c) := by omega
    have hf4 : ¬ (b ≤ c ∧ c ≤ a) := by omega
    have hf5 : ¬ (c ≤ a ∧ a ≤ b) := by omega
    have hf6 : ¬ (c ≤ b ∧ b ≤ a) := by omega
    rw [ite_eq_left ⟨le_of_lt hab, le_of_lt hbc⟩, ite_eq_left ⟨hab, hbc⟩,
        ite_eq_right hf2, ite_eq_right hf3, ite_eq_right hf4, ite_eq_right hf5, ite_eq_right hf6]
    ring

private lemma ordWeight_symm_sum (a b c : ℕ) :
    T a b c =
      ordWeight (a, b, c) + ordWeight (a, c, b) + ordWeight (b, a, c) +
      ordWeight (b, c, a) + ordWeight (c, a, b) + ordWeight (c, b, a) := by
  rcases le_total a b with h1 | h1 <;>
  rcases le_total b c with h2 | h2 <;>
  rcases le_total a c with h3 | h3
  · exact ordWeight_symm_ordered h1 h2
  · exact ordWeight_symm_ordered h1 h2
  · have he := ordWeight_symm_ordered h3 h2; rw [T_symm_23 a c b] at he; linarith
  · have he := ordWeight_symm_ordered h3 h1; rw [T_symm_cyc c a b] at he; linarith
  · have he := ordWeight_symm_ordered h1 h3; rw [T_symm_12 b a c] at he; linarith
  · have he := ordWeight_symm_ordered h2 h3; rw [← T_symm_cyc a b c] at he; linarith
  · have he := ordWeight_symm_ordered h2 h1; rw [T_symm_13 c b a] at he; linarith
  · have he := ordWeight_symm_ordered h2 h1; rw [T_symm_13 c b a] at he; linarith

/-- Exact 6-way partition of `bulkSum L` on `simplex3 (L - 1)`. -/
lemma bulkSum_eq_partition (L : ℕ) (hL : 3 ≤ L) :
    bulkSum L =
      (3 : ℝ) ^ (L - 1) / (6 * ((L - 1).factorial : ℝ)) -
      (1 / 2 : ℝ) * (∑ x ∈ Finset.range ((L - 1) / 2 + 1),
        (if 3 * x > L - 1 then T x x (L - 1 - 2 * x)
         else if 3 * x < L - 1 then -T x x (L - 1 - 2 * x) else 0)) -
      (∑ a ∈ Finset.range ((L - 1) / 3 + 1), extraOddTerm L a) -
      (if (L - 1) % 3 = 1 then T ((L - 2) / 3) ((L - 2) / 3) ((L - 2) / 3 + 1) else 0) -
      (if (L - 1) % 3 = 0 then (1 / 6 : ℝ) * T ((L - 1) / 3) ((L - 1) / 3) ((L - 1) / 3) else 0) := by
  set m := L - 1
  have hbulk_m : bulkSum L =
      ∑ t ∈ (simplex3 m).filter (fun t => t.1 ≤ t.2.1 ∧ t.2.1 + 2 ≤ t.2.2), T t.1 t.2.1 t.2.2 := by
    unfold bulkSum
    refine Finset.sum_bij (fun t _ => (t.1, t.2.1 - 1, t.2.2)) ?_ ?_ ?_ ?_
    · intro ⟨a, b, c⟩ ht; rw [mem_filter, mem_simplex3] at ht ⊢; dsimp only at ht ⊢; omega
    · intro ⟨a1, b1, c1⟩ ht1 ⟨a2, b2, c2⟩ ht2 h
      rw [mem_filter, mem_simplex3_mk] at ht1 ht2
      simp only [Prod.mk.injEq] at h
      rcases ht1 with ⟨ht1s, ht1a, ht1b⟩
      rcases ht2 with ⟨ht2s, ht2a, ht2b⟩
      change a1 < b1 at ht1a; change b1 < c1 at ht1b
      change a2 < b2 at ht2a; change b2 < c2 at ht2b
      obtain ⟨rfl, h2, rfl⟩ := h
      simp only [Prod.mk.injEq]; exact ⟨trivial, by omega, trivial⟩
    · intro ⟨a, b, c⟩ ht
      rw [mem_filter, mem_simplex3] at ht; dsimp only at ht
      refine ⟨(a, b + 1, c), ?_, by simp⟩
      rw [mem_filter, mem_simplex3]; dsimp only; omega
    · intro _ _; rfl
  rw [hbulk_m]
  let ord := (simplex3 m).filter (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)
  have hfull : (3 : ℝ) ^ m / (6 * (m.factorial : ℝ)) =
      ∑ t ∈ ord,
        (if t.1 < t.2.1 ∧ t.2.1 < t.2.2 then (1 : ℝ)
         else if t.1 = t.2.1 ∧ t.2.1 = t.2.2 then (1 / 6 : ℝ)
         else (1 / 2 : ℝ)) * T t.1 t.2.1 t.2.2 := by
    have h6 : (3 : ℝ) ^ m / (m.factorial : ℝ) = ∑ t ∈ simplex3 m, T t.1 t.2.1 t.2.2 :=
      (sum_simplex3_T m).symm
    have hsum6 : ∑ t ∈ simplex3 m, T t.1 t.2.1 t.2.2 = 6 * ∑ t ∈ simplex3 m, ordWeight t := by
      have hs : ∑ t ∈ simplex3 m, T t.1 t.2.1 t.2.2 =
          (∑ t ∈ simplex3 m, ordWeight (t.1, t.2.1, t.2.2)) +
          (∑ t ∈ simplex3 m, ordWeight (t.1, t.2.2, t.2.1)) +
          (∑ t ∈ simplex3 m, ordWeight (t.2.1, t.1, t.2.2)) +
          (∑ t ∈ simplex3 m, ordWeight (t.2.1, t.2.2, t.1)) +
          (∑ t ∈ simplex3 m, ordWeight (t.2.2, t.1, t.2.1)) +
          (∑ t ∈ simplex3 m, ordWeight (t.2.2, t.2.1, t.1)) := by
        simp_rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun t _ => ordWeight_symm_sum t.1 t.2.1 t.2.2
      rw [hs, sum_simplex3_swap23 m ordWeight, sum_simplex3_swap12 m ordWeight,
          sum_simplex3_cyc m ordWeight, sum_simplex3_cyc2 m ordWeight, sum_simplex3_swap13 m ordWeight]
      ring
    have hword : ∑ t ∈ simplex3 m, ordWeight t =
        ∑ t ∈ ord,
          (if t.1 < t.2.1 ∧ t.2.1 < t.2.2 then (1 : ℝ)
           else if t.1 = t.2.1 ∧ t.2.1 = t.2.2 then (1 / 6 : ℝ)
           else (1 / 2 : ℝ)) * T t.1 t.2.1 t.2.2 := by
      simp only [ord, Finset.sum_filter, ordWeight]
    rw [← hword]
    have : (3 : ℝ) ^ m / (6 * (m.factorial : ℝ)) = ((3 : ℝ) ^ m / (m.factorial : ℝ)) / 6 := by ring
    rw [this, h6, hsum6]; ring
  have hsub_ord :
      ∑ t ∈ (simplex3 m).filter (fun t => t.1 ≤ t.2.1 ∧ t.2.1 + 2 ≤ t.2.2), T t.1 t.2.1 t.2.2 =
      ∑ t ∈ ord, (if t.2.1 + 2 ≤ t.2.2 then (1 : ℝ) else 0) * T t.1 t.2.1 t.2.2 := by
    simp only [ord, Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> first | omega | ring
  rw [hsub_ord, hfull]
  have hdiff_ord :
      (∑ t ∈ ord, (if t.2.1 + 2 ≤ t.2.2 then (1 : ℝ) else 0) * T t.1 t.2.1 t.2.2) -
      (∑ t ∈ ord,
        (if t.1 < t.2.1 ∧ t.2.1 < t.2.2 then (1 : ℝ)
         else if t.1 = t.2.1 ∧ t.2.1 = t.2.2 then (1 / 6 : ℝ)
         else (1 / 2 : ℝ)) * T t.1 t.2.1 t.2.2) =
      (∑ t ∈ ord, (if t.1 = t.2.1 ∧ t.2.1 + 2 ≤ t.2.2 then (1 / 2 : ℝ) * T t.1 t.2.1 t.2.2 else 0)) -
      (∑ t ∈ ord, (if t.1 < t.2.1 ∧ t.2.1 = t.2.2 then (1 / 2 : ℝ) * T t.1 t.2.1 t.2.2 else 0)) -
      (∑ t ∈ ord, (if t.1 < t.2.1 ∧ t.2.1 + 1 = t.2.2 then T t.1 t.2.1 t.2.2 else 0)) -
      (∑ t ∈ ord, (if t.1 = t.2.1 ∧ t.2.1 + 1 = t.2.2 then (1 / 2 : ℝ) * T t.1 t.2.1 t.2.2 else 0)) -
      (∑ t ∈ ord, (if t.1 = t.2.1 ∧ t.2.1 = t.2.2 then (1 / 6 : ℝ) * T t.1 t.2.1 t.2.2 else 0)) := by
    simp_rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    simp only [ord, mem_filter] at ht
    rcases ht with ⟨_, h1, h2⟩
    split_ifs <;> first | omega | ring
  have hsgn :
      (∑ t ∈ ord, (if t.1 < t.2.1 ∧ t.2.1 = t.2.2 then (1 / 2 : ℝ) * T t.1 t.2.1 t.2.2 else 0)) -
      (∑ t ∈ ord, (if t.1 = t.2.1 ∧ t.2.1 + 2 ≤ t.2.2 then (1 / 2 : ℝ) * T t.1 t.2.1 t.2.2 else 0)) -
      (∑ t ∈ ord, (if t.1 = t.2.1 ∧ t.2.1 + 1 = t.2.2 then (1 / 2 : ℝ) * T t.1 t.2.1 t.2.2 else 0)) =
      (1 / 2 : ℝ) * (∑ x ∈ Finset.range (m / 2 + 1),
        (if 3 * x > m then T x x (m - 2 * x)
         else if 3 * x < m then -T x x (m - 2 * x) else 0)) := by
    have hsplit1D :
        (1 / 2 : ℝ) * (∑ x ∈ Finset.range (m / 2 + 1),
          (if 3 * x > m then T x x (m - 2 * x)
           else if 3 * x < m then -T x x (m - 2 * x) else 0)) =
        (∑ x ∈ (Finset.range (m / 2 + 1)).filter (fun x => 3 * x > m), (1 / 2 : ℝ) * T x x (m - 2 * x)) -
        (∑ x ∈ (Finset.range (m / 2 + 1)).filter (fun x => 3 * x < m), (1 / 2 : ℝ) * T x x (m - 2 * x)) := by
      rw [Finset.mul_sum, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> first | omega | ring
    rw [hsplit1D]
    have hgt : ∑ t ∈ ord, (if t.1 < t.2.1 ∧ t.2.1 = t.2.2 then (1 / 2 : ℝ) * T t.1 t.2.1 t.2.2 else 0) =
        ∑ x ∈ (Finset.range (m / 2 + 1)).filter (fun x => 3 * x > m), (1 / 2 : ℝ) * T x x (m - 2 * x) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun t _ => t.2.1) ?_ ?_ ?_ ?_
      · intro ⟨a, b, c⟩ ht
        simp only [ord, mem_filter, mem_simplex3_mk, mem_range] at ht ⊢
        rcases ht with ⟨⟨hsum, hab, hbc⟩, hlt, heq⟩
        change a ≤ b at hab; change b ≤ c at hbc; change a < b at hlt; change b = c at heq
        omega
      · intro ⟨a1, b1, c1⟩ ht1 ⟨a2, b2, c2⟩ ht2 h
        simp only [ord, mem_filter, mem_simplex3_mk] at ht1 ht2
        rcases ht1 with ⟨⟨hsum1, _, _⟩, _, heq1⟩
        rcases ht2 with ⟨⟨hsum2, _, _⟩, _, heq2⟩
        change b1 = c1 at heq1; change b2 = c2 at heq2; change b1 = b2 at h
        simp only [Prod.mk.injEq]; exact ⟨by omega, h, by omega⟩
      · intro x hx
        simp only [mem_filter, mem_range] at hx
        refine ⟨(m - 2 * x, x, x), ?_, rfl⟩
        simp only [ord, mem_filter, mem_simplex3_mk]
        have hm_eq : m = L - 1 := rfl
        exact ⟨⟨by omega, by omega, le_rfl⟩, by omega, trivial⟩
      · intro ⟨a, b, c⟩ ht
        simp only [ord, mem_filter, mem_simplex3_mk] at ht
        rcases ht with ⟨⟨hsum, _, _⟩, _, heq⟩
        change b = c at heq
        have ha : a = m - 2 * b := by omega
        have hc : c = b := by omega
        dsimp only; rw [ha, hc, T_symm_cyc]
    have hlt :
        (∑ t ∈ ord, (if t.1 = t.2.1 ∧ t.2.1 + 2 ≤ t.2.2 then (1 / 2 : ℝ) * T t.1 t.2.1 t.2.2 else 0)) +
        (∑ t ∈ ord, (if t.1 = t.2.1 ∧ t.2.1 + 1 = t.2.2 then (1 / 2 : ℝ) * T t.1 t.2.1 t.2.2 else 0)) =
        ∑ x ∈ (Finset.range (m / 2 + 1)).filter (fun x => 3 * x < m), (1 / 2 : ℝ) * T x x (m - 2 * x) := by
      rw [← Finset.sum_add_distrib]
      have hcomb : ∑ t ∈ ord,
          ((if t.1 = t.2.1 ∧ t.2.1 + 2 ≤ t.2.2 then (1 / 2 : ℝ) * T t.1 t.2.1 t.2.2 else 0) +
           (if t.1 = t.2.1 ∧ t.2.1 + 1 = t.2.2 then (1 / 2 : ℝ) * T t.1 t.2.1 t.2.2 else 0)) =
          ∑ t ∈ ord.filter (fun t => t.1 = t.2.1 ∧ t.2.1 < t.2.2), (1 / 2 : ℝ) * T t.1 t.2.1 t.2.2 := by
        conv_rhs => rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun t _ => ?_
        split_ifs <;> first | omega | ring
      rw [hcomb]
      refine Finset.sum_bij (fun t _ => t.1) ?_ ?_ ?_ ?_
      · intro ⟨a, b, c⟩ ht
        simp only [ord, mem_filter, mem_simplex3_mk, mem_range] at ht ⊢
        rcases ht with ⟨⟨hsum, hab, hbc⟩, heq, hlt⟩
        change a = b at heq; change b < c at hlt
        omega
      · intro ⟨a1, b1, c1⟩ ht1 ⟨a2, b2, c2⟩ ht2 h
        simp only [ord, mem_filter, mem_simplex3_mk] at ht1 ht2
        rcases ht1 with ⟨⟨hsum1, _, _⟩, heq1, _⟩
        rcases ht2 with ⟨⟨hsum2, _, _⟩, heq2, _⟩
        change a1 = b1 at heq1; change a2 = b2 at heq2; change a1 = a2 at h
        simp only [Prod.mk.injEq]; exact ⟨h, by omega, by omega⟩
      · intro x hx
        simp only [mem_filter, mem_range] at hx
        refine ⟨(x, x, m - 2 * x), ?_, rfl⟩
        simp only [ord, mem_filter, mem_simplex3_mk]
        have hm_eq : m = L - 1 := rfl
        exact ⟨⟨by omega, le_rfl, by omega⟩, trivial, by omega⟩
      · intro ⟨a, b, c⟩ ht
        simp only [ord, mem_filter, mem_simplex3_mk] at ht
        rcases ht with ⟨⟨hsum, _, _⟩, heq, _⟩
        change a = b at heq
        have hb : b = a := by omega
        have hc : c = m - 2 * a := by omega
        dsimp only; rw [hb, hc]
    linarith
  have hextra :
      ∑ t ∈ ord, (if t.1 < t.2.1 ∧ t.2.1 + 1 = t.2.2 then T t.1 t.2.1 t.2.2 else 0) =
      ∑ a ∈ Finset.range ((L - 1) / 3 + 1), extraOddTerm L a := by
    rw [← Finset.sum_filter]
    have hfilt : ∑ a ∈ Finset.range ((L - 1) / 3 + 1), extraOddTerm L a =
        ∑ a ∈ (Finset.range ((L - 1) / 3 + 1)).filter (fun a => (L - a) % 2 = 1 ∧ 1 ≤ a),
          T (a - 1) ((L - a - 1) / 2) ((L - a - 1) / 2 + 1) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => rfl
    rw [hfilt]
    refine Finset.sum_bij (fun t _ => t.1 + 1) ?_ ?_ ?_ ?_
    · intro ⟨a, b, c⟩ ht
      simp only [ord, mem_filter, mem_simplex3_mk, mem_range] at ht ⊢
      rcases ht with ⟨⟨hsum, _, _⟩, hlt, hsucc⟩
      change a < b at hlt; change b + 1 = c at hsucc
      have hm_eq : m = L - 1 := rfl
      omega
    · intro ⟨a1, b1, c1⟩ ht1 ⟨a2, b2, c2⟩ ht2 h
      simp only [ord, mem_filter, mem_simplex3_mk] at ht1 ht2
      rcases ht1 with ⟨⟨hsum1, _, _⟩, _, hsucc1⟩
      rcases ht2 with ⟨⟨hsum2, _, _⟩, _, hsucc2⟩
      change b1 + 1 = c1 at hsucc1; change b2 + 1 = c2 at hsucc2; change a1 + 1 = a2 + 1 at h
      simp only [Prod.mk.injEq]; exact ⟨by omega, by omega, by omega⟩
    · intro a ha
      simp only [mem_filter, mem_range] at ha
      refine ⟨(a - 1, (L - a - 1) / 2, (L - a - 1) / 2 + 1), ?_, by omega⟩
      simp only [ord, mem_filter, mem_simplex3_mk]
      have hm_eq : m = L - 1 := rfl
      exact ⟨⟨by omega, by omega, by omega⟩, by omega, trivial⟩
    · intro ⟨a, b, c⟩ ht
      simp only [ord, mem_filter, mem_simplex3_mk] at ht
      rcases ht with ⟨⟨hsum, _, _⟩, hlt, hsucc⟩
      change a < b at hlt; change b + 1 = c at hsucc
      have hm_eq : m = L - 1 := rfl
      have h1 : a + 1 - 1 = a := by omega
      have h2 : (L - (a + 1) - 1) / 2 = b := by omega
      have hc : c = b + 1 := by omega
      dsimp only; rw [h1, h2, hc]
  have heqadj :
      ∑ t ∈ ord, (if t.1 = t.2.1 ∧ t.2.1 + 1 = t.2.2 then (1 / 2 : ℝ) * T t.1 t.2.1 t.2.2 else 0) =
      if m % 3 = 1 then (1 / 2 : ℝ) * T ((L - 2) / 3) ((L - 2) / 3) ((L - 2) / 3 + 1) else 0 := by
    rw [← Finset.sum_filter]
    by_cases hmod : m % 3 = 1
    · rw [ite_eq_left hmod]
      have hsing : ord.filter (fun t => t.1 = t.2.1 ∧ t.2.1 + 1 = t.2.2) =
          {((L - 2) / 3, (L - 2) / 3, (L - 2) / 3 + 1)} := by
        ext ⟨a, b, c⟩
        simp only [ord, mem_filter, mem_simplex3_mk, mem_singleton, Prod.mk.injEq]
        have hm_eq : m = L - 1 := rfl
        constructor
        · rintro ⟨⟨hsum, _, _⟩, heq, hsucc⟩
          change a = b at heq; change b + 1 = c at hsucc
          omega
        · rintro ⟨rfl, rfl, rfl⟩
          exact ⟨⟨by omega, le_rfl, by omega⟩, rfl, rfl⟩
      rw [hsing, Finset.sum_singleton]
    · rw [ite_eq_right hmod]
      have hemp : ord.filter (fun t => t.1 = t.2.1 ∧ t.2.1 + 1 = t.2.2) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro ⟨a, b, c⟩ ht
        simp only [ord, mem_filter, mem_simplex3_mk] at ht
        rintro ⟨heq, hsucc⟩
        change a = b at heq; change b + 1 = c at hsucc
        omega
      rw [hemp, Finset.sum_empty]
  have halleq :
      ∑ t ∈ ord, (if t.1 = t.2.1 ∧ t.2.1 = t.2.2 then (1 / 6 : ℝ) * T t.1 t.2.1 t.2.2 else 0) =
      if m % 3 = 0 then (1 / 6 : ℝ) * T (m / 3) (m / 3) (m / 3) else 0 := by
    rw [← Finset.sum_filter]
    by_cases hmod : m % 3 = 0
    · rw [ite_eq_left hmod]
      have hsing : ord.filter (fun t => t.1 = t.2.1 ∧ t.2.1 = t.2.2) = {(m / 3, m / 3, m / 3)} := by
        ext ⟨a, b, c⟩
        simp only [ord, mem_filter, mem_simplex3_mk, mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨hsum, _, _⟩, heq1, heq2⟩
          change a = b at heq1; change b = c at heq2
          omega
        · rintro ⟨rfl, rfl, rfl⟩
          exact ⟨⟨by omega, le_rfl, le_rfl⟩, rfl, rfl⟩
      rw [hsing, Finset.sum_singleton]
    · rw [ite_eq_right hmod]
      have hemp : ord.filter (fun t => t.1 = t.2.1 ∧ t.2.1 = t.2.2) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro ⟨a, b, c⟩ ht
        simp only [ord, mem_filter, mem_simplex3_mk] at ht
        rintro ⟨heq1, heq2⟩
        change a = b at heq1; change b = c at heq2
        omega
      rw [hemp, Finset.sum_empty]
  have h2eq : 2 * (if m % 3 = 1 then (1 / 2 : ℝ) * T ((L - 2) / 3) ((L - 2) / 3) ((L - 2) / 3 + 1) else 0) =
      if m % 3 = 1 then T ((L - 2) / 3) ((L - 2) / 3) ((L - 2) / 3 + 1) else 0 := by
    split_ifs <;> ring
  linarith

/-- Master exact 1D reduction for `uvSum L` (for every `L ≥ 3`). -/
lemma uvSum_master (L : ℕ) (hL : 3 ≤ L) :
    uvSum L =
      -(3 : ℝ) ^ (L - 1) / (6 * ((L - 1).factorial : ℝ)) +
      (1 / 2 : ℝ) * (∑ x ∈ Finset.range ((L - 1) / 2 + 1),
        (if 3 * x > L - 1 then T x x (L - 1 - 2 * x)
         else if 3 * x < L - 1 then -T x x (L - 1 - 2 * x) else 0)) +
      PhiNat L ((L - 1) / 3 + 1) +
      (if (L - 1) % 3 = 1 then T ((L - 2) / 3) ((L - 2) / 3) ((L - 2) / 3 + 1) else 0) +
      (if (L - 1) % 3 = 0 then (1 / 6 : ℝ) * T ((L - 1) / 3) ((L - 1) / 3) ((L - 1) / 3) else 0) := by
  have h1 := uvSum_eq_bdry_sub_bulk L hL
  have h2 := bulkSum_eq_partition L hL
  have htel : (∑ a ∈ Finset.range ((L - 1) / 3 + 1), bdryTerm L a) +
      (∑ a ∈ Finset.range ((L - 1) / 3 + 1), extraOddTerm L a) =
      PhiNat L ((L - 1) / 3 + 1) := by
    rw [← Finset.sum_add_distrib]
    have hcongr : ∑ a ∈ Finset.range ((L - 1) / 3 + 1), (bdryTerm L a + extraOddTerm L a) =
        ∑ a ∈ Finset.range ((L - 1) / 3 + 1), (PhiNat L (a + 1) - PhiNat L a) := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [mem_range] at ha
      exact bdry_add_extra_eq_PhiNat_sub L a hL (by omega)
    rw [hcongr, Finset.sum_range_sub (PhiNat L) ((L - 1) / 3 + 1)]
    simp [PhiNat]
  rw [neg_div]
  linarith

/-! ### Part 4: Exact formulas for the three residue classes `3q`, `3q + 1`, `3q - 1` -/

/-- Signed 1D trinomial sum splitting `3 * x` above and below `m`. -/
noncomputable def sgnSum (m : ℕ) : ℝ :=
  ∑ x ∈ Finset.range (m / 2 + 1),
    (if 3 * x > m then T x x (m - 2 * x)
     else if 3 * x < m then -T x x (m - 2 * x) else 0)

lemma hAdj_eq_sgnSum (L : ℕ) (hL : 3 ≤ L) :
    hAdj L = (L : ℝ) / 9 +
      2 * ((L.factorial : ℝ) / (3 : ℝ) ^ L) * sgnSum (L - 1) +
      4 * ((L.factorial : ℝ) / (3 : ℝ) ^ L) *
        (PhiNat L ((L - 1) / 3 + 1) +
         (if (L - 1) % 3 = 1 then T ((L - 2) / 3) ((L - 2) / 3) ((L - 2) / 3 + 1) else 0) +
         (if (L - 1) % 3 = 0 then (1 / 6 : ℝ) * T ((L - 1) / 3) ((L - 1) / 3) ((L - 1) / 3) else 0)) := by
  rw [hAdj_eq_uvSum L (by omega), uvSum_master L hL]
  unfold sgnSum
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.factorial_succ, pow_succ]
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  have h3 : (3 : ℝ) ^ m ≠ 0 := by positivity
  push_cast; field_simp; ring

lemma p3q_eq_of_le {q x : ℕ} (hx : 2 * x ≤ 3 * q) :
    p3q q x = ((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q) * T x x (3 * q - 2 * x) := by
  unfold p3q; rw [ite_eq_left hx]

lemma p3q_eq_zero_of_gt {q x : ℕ} (hx : 3 * q < 2 * x) : p3q q x = 0 := by
  unfold p3q; rw [ite_eq_right (by omega)]

lemma sgnSum_3q (q : ℕ) :
    ((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q) * sgnSum (3 * q) = p3q q q * sumA q := by
  have hp0 : p3q q q ≠ 0 := ne_of_gt (p3q_center_pos q)
  unfold sumA
  rw [mul_div_cancel₀ _ hp0]
  unfold sgnSum
  rw [Finset.mul_sum]
  have hsplit : ∑ x ∈ Finset.range (3 * q / 2 + 1),
      ((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q) *
        (if 3 * x > 3 * q then T x x (3 * q - 2 * x)
         else if 3 * x < 3 * q then -T x x (3 * q - 2 * x) else 0) =
      (∑ x ∈ (Finset.range (3 * q / 2 + 1)).filter (fun x => q < x), p3q q x) -
      (∑ x ∈ (Finset.range (3 * q / 2 + 1)).filter (fun x => x < q), p3q q x) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_range] at hx
    have h2x : 2 * x ≤ 3 * q := by omega
    rw [p3q_eq_of_le h2x]
    split_ifs <;> first | omega | ring
  rw [hsplit, Finset.sum_sub_distrib]
  congr 1
  · rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 q) (fun k => 2 * k ≤ q)]
    have hzero : ∑ k ∈ (Finset.Icc 1 q).filter (fun k => ¬ 2 * k ≤ q), p3q q (q + k) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [mem_filter] at hk
      exact p3q_eq_zero_of_gt (by omega)
    rw [hzero, add_zero]
    refine Finset.sum_bij (fun x _ => x - q) ?_ ?_ ?_ ?_
    · intro x hx; rw [mem_filter, mem_range] at hx; rw [mem_filter, mem_Icc]; omega
    · intro x1 hx1 x2 hx2 h; rw [mem_filter] at hx1 hx2; omega
    · intro k hk; rw [mem_filter, mem_Icc] at hk
      exact ⟨q + k, by rw [mem_filter, mem_range]; omega, by omega⟩
    · intro x hx; rw [mem_filter] at hx; congr 1; omega
  · refine Finset.sum_bij (fun x _ => q - x) ?_ ?_ ?_ ?_
    · intro x hx; rw [mem_filter, mem_range] at hx; rw [mem_Icc]; omega
    · intro x1 hx1 x2 hx2 h; rw [mem_filter] at hx1 hx2; omega
    · intro k hk; rw [mem_Icc] at hk
      exact ⟨q - k, by rw [mem_filter, mem_range]; omega, by omega⟩
    · intro x hx; rw [mem_filter] at hx; congr 1; omega

lemma step_3q_sub_1 (q x : ℕ) (hq : 1 ≤ q) (hx : 2 * x ≤ 3 * q - 1) :
    ((3 * q - 1).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 1) * T x x (3 * q - 1 - 2 * x) =
      (((3 * q - 2 * x : ℕ) : ℝ) / (q : ℝ)) * p3q q x := by
  have h2x : 2 * x ≤ 3 * q := by omega
  rw [p3q_eq_of_le h2x]
  obtain ⟨c, hc⟩ : ∃ c, 3 * q - 2 * x = c + 1 := ⟨3 * q - 2 * x - 1, by omega⟩
  have hc' : 3 * q - 1 - 2 * x = c := by omega
  obtain ⟨m, hm⟩ : ∃ m, 3 * q = m + 1 := ⟨3 * q - 1, by omega⟩
  have hm' : 3 * q - 1 = m := by omega
  rw [hc', hm']
  have hT : (((3 * q - 2 * x : ℕ) : ℝ)) * T x x (3 * q - 2 * x) = T x x c := by
    rw [hc]; exact mul_T_thd x x c
  have hfact : ((3 * q).factorial : ℝ) = (3 * (q : ℝ)) * (m.factorial : ℝ) := by
    rw [hm, Nat.factorial_succ]
    have hmR : (m : ℝ) + 1 = 3 * (q : ℝ) := by exact_mod_cast hm.symm
    push_cast
    rw [hmR]
  have hpow : (3 : ℝ) ^ (3 * q) = 3 * (3 : ℝ) ^ m := by
    rw [hm, pow_succ]; ring
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have h3m : (3 : ℝ) ^ m ≠ 0 := by positivity
  calc (m.factorial : ℝ) / (3 : ℝ) ^ m * T x x c
      = (m.factorial : ℝ) / (3 : ℝ) ^ m * ((((3 * q - 2 * x : ℕ) : ℝ)) * T x x (3 * q - 2 * x)) := by
        rw [hT]
    _ = (((3 * q - 2 * x : ℕ) : ℝ) / (q : ℝ)) *
          (((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q) * T x x (3 * q - 2 * x)) := by
        rw [hfact, hpow]; field_simp

lemma sgnSum_3q_sub_1 (q : ℕ) (hq : 1 ≤ q) :
    ((3 * q - 1).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 1) * sgnSum (3 * q - 1) =
      p3q q q * (1 + sumA q - 2 * sumB q) := by
  have hp0 : p3q q q ≠ 0 := ne_of_gt (p3q_center_pos q)
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  unfold sumA sumB
  have hrhs : p3q q q * (1 + (∑ k ∈ Finset.Icc 1 q, (p3q q (q + k) - p3q q (q - k))) / p3q q q -
      2 * ((∑ k ∈ Finset.Icc 1 q, ((k : ℝ) / (q : ℝ)) * (p3q q (q + k) + p3q q (q - k))) / p3q q q)) =
      p3q q q + ∑ k ∈ Finset.Icc 1 q,
        ((1 - 2 * (k : ℝ) / (q : ℝ)) * p3q q (q + k) - (1 + 2 * (k : ℝ) / (q : ℝ)) * p3q q (q - k)) := by
    have hmul : p3q q q * (1 + (∑ k ∈ Finset.Icc 1 q, (p3q q (q + k) - p3q q (q - k))) / p3q q q -
        2 * ((∑ k ∈ Finset.Icc 1 q, ((k : ℝ) / (q : ℝ)) * (p3q q (q + k) + p3q q (q - k))) / p3q q q)) =
        p3q q q + ((∑ k ∈ Finset.Icc 1 q, (p3q q (q + k) - p3q q (q - k))) -
        2 * (∑ k ∈ Finset.Icc 1 q, ((k : ℝ) / (q : ℝ)) * (p3q q (q + k) + p3q q (q - k)))) := by
      field_simp; ring
    rw [hmul]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hrhs]
  unfold sgnSum
  rw [Finset.mul_sum]
  have hsplit : ∑ x ∈ Finset.range ((3 * q - 1) / 2 + 1),
      ((3 * q - 1).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 1) *
        (if 3 * x > 3 * q - 1 then T x x (3 * q - 1 - 2 * x)
         else if 3 * x < 3 * q - 1 then -T x x (3 * q - 1 - 2 * x) else 0) =
      p3q q q +
      (∑ x ∈ (Finset.range ((3 * q - 1) / 2 + 1)).filter (fun x => q < x),
        (((3 * q - 2 * x : ℕ) : ℝ) / (q : ℝ)) * p3q q x) -
      (∑ x ∈ (Finset.range ((3 * q - 1) / 2 + 1)).filter (fun x => x < q),
        (((3 * q - 2 * x : ℕ) : ℝ) / (q : ℝ)) * p3q q x) := by
    have hq_mem : q ∈ Finset.range ((3 * q - 1) / 2 + 1) := by rw [mem_range]; omega
    have hq_term : ((3 * q - 1).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 1) *
        (if 3 * q > 3 * q - 1 then T q q (3 * q - 1 - 2 * q)
         else if 3 * q < 3 * q - 1 then -T q q (3 * q - 1 - 2 * q) else 0) = p3q q q := by
      rw [ite_eq_left (by omega), step_3q_sub_1 q q hq (by omega)]
      have : 3 * q - 2 * q = q := by omega
      rw [this, div_self hq0, one_mul]
    rw [← Finset.add_sum_erase _ _ hq_mem, hq_term]
    have hrest : ∑ x ∈ (Finset.range ((3 * q - 1) / 2 + 1)).erase q,
        ((3 * q - 1).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 1) *
          (if 3 * x > 3 * q - 1 then T x x (3 * q - 1 - 2 * x)
           else if 3 * x < 3 * q - 1 then -T x x (3 * q - 1 - 2 * x) else 0) =
        (∑ x ∈ (Finset.range ((3 * q - 1) / 2 + 1)).filter (fun x => q < x),
          (((3 * q - 2 * x : ℕ) : ℝ) / (q : ℝ)) * p3q q x) -
        (∑ x ∈ (Finset.range ((3 * q - 1) / 2 + 1)).filter (fun x => x < q),
          (((3 * q - 2 * x : ℕ) : ℝ) / (q : ℝ)) * p3q q x) := by
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
      have herase := Finset.add_sum_erase (Finset.range ((3 * q - 1) / 2 + 1))
        (fun x => (if q < x then (((3 * q - 2 * x : ℕ) : ℝ) / (q : ℝ)) * p3q q x else 0) -
                  (if x < q then (((3 * q - 2 * x : ℕ) : ℝ) / (q : ℝ)) * p3q q x else 0)) hq_mem
      simp only [lt_irrefl, ↓reduceIte, sub_self, zero_add] at herase
      rw [← herase]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [mem_erase, mem_range] at hx
      have h2x : 2 * x ≤ 3 * q - 1 := by omega
      by_cases hgt : q < x
      · rw [ite_eq_left (by omega), ite_eq_left hgt, ite_eq_right (by omega), sub_zero]
        exact step_3q_sub_1 q x hq h2x
      · have hlt : x < q := by omega
        rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right hgt, ite_eq_left hlt, zero_sub, mul_neg]
        congr 1
        exact step_3q_sub_1 q x hq h2x
    linarith
  rw [hsplit, Finset.sum_sub_distrib]
  have hright :
      ∑ x ∈ (Finset.range ((3 * q - 1) / 2 + 1)).filter (fun x => q < x),
        (((3 * q - 2 * x : ℕ) : ℝ) / (q : ℝ)) * p3q q x =
      ∑ k ∈ Finset.Icc 1 q, (1 - 2 * (k : ℝ) / (q : ℝ)) * p3q q (q + k) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 q) (fun k => 2 * k ≤ q - 1)]
    have hzero : ∑ k ∈ (Finset.Icc 1 q).filter (fun k => ¬ 2 * k ≤ q - 1),
        (1 - 2 * (k : ℝ) / (q : ℝ)) * p3q q (q + k) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [mem_filter, mem_Icc] at hk
      by_cases heq : 2 * k = q
      · have : (1 - 2 * (k : ℝ) / (q : ℝ)) = 0 := by
          have : (2 * k : ℝ) = (q : ℝ) := by exact_mod_cast heq
          field_simp; linarith
        rw [this, zero_mul]
      · rw [p3q_eq_zero_of_gt (by omega), mul_zero]
    rw [hzero, add_zero]
    refine Finset.sum_bij (fun x _ => x - q) ?_ ?_ ?_ ?_
    · intro x hx; rw [mem_filter, mem_range] at hx; rw [mem_filter, mem_Icc]; omega
    · intro x1 hx1 x2 hx2 h; rw [mem_filter] at hx1 hx2; omega
    · intro k hk; rw [mem_filter, mem_Icc] at hk
      exact ⟨q + k, by rw [mem_filter, mem_range]; omega, by omega⟩
    · intro x hx
      rw [mem_filter, mem_range] at hx
      have h1 : q + (x - q) = x := by omega
      have h2 : ((3 * q - 2 * x : ℕ) : ℝ) / (q : ℝ) = 1 - 2 * ((x - q : ℕ) : ℝ) / (q : ℝ) := by
        have : (3 * q - 2 * x : ℕ) + 2 * (x - q) = q := by omega
        have hR : ((3 * q - 2 * x : ℕ) : ℝ) + 2 * ((x - q : ℕ) : ℝ) = (q : ℝ) := by exact_mod_cast this
        field_simp; linarith
      rw [h1, h2]
  have hleft :
      ∑ x ∈ (Finset.range ((3 * q - 1) / 2 + 1)).filter (fun x => x < q),
        (((3 * q - 2 * x : ℕ) : ℝ) / (q : ℝ)) * p3q q x =
      ∑ k ∈ Finset.Icc 1 q, (1 + 2 * (k : ℝ) / (q : ℝ)) * p3q q (q - k) := by
    refine Finset.sum_bij (fun x _ => q - x) ?_ ?_ ?_ ?_
    · intro x hx; rw [mem_filter, mem_range] at hx; rw [mem_Icc]; omega
    · intro x1 hx1 x2 hx2 h; rw [mem_filter] at hx1 hx2; omega
    · intro k hk; rw [mem_Icc] at hk
      exact ⟨q - k, by rw [mem_filter, mem_range]; omega, by omega⟩
    · intro x hx
      rw [mem_filter, mem_range] at hx
      have h1 : q - (q - x) = x := by omega
      have h2 : ((3 * q - 2 * x : ℕ) : ℝ) / (q : ℝ) = 1 + 2 * ((q - x : ℕ) : ℝ) / (q : ℝ) := by
        have : (3 * q - 2 * x : ℕ) = q + 2 * (q - x) := by omega
        have hR : ((3 * q - 2 * x : ℕ) : ℝ) = (q : ℝ) + 2 * ((q - x : ℕ) : ℝ) := by exact_mod_cast this
        field_simp; linarith
      rw [h1, h2]
  rw [hright, hleft]; ring

lemma step_3q_sub_2 (q x : ℕ) (hq : 2 ≤ q) (hx : 2 * x ≤ 3 * q - 2) :
    ((3 * q - 2).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 2) * T x x (3 * q - 2 - 2 * x) =
      (3 * ((3 * q - 2 * x : ℕ) : ℝ) * ((3 * q - 1 - 2 * x : ℕ) : ℝ) /
        ((q : ℝ) * (3 * (q : ℝ) - 1))) * p3q q x := by
  have h2x : 2 * x ≤ 3 * q := by omega
  rw [p3q_eq_of_le h2x]
  obtain ⟨c, hc⟩ : ∃ c, 3 * q - 2 * x = c + 2 := ⟨3 * q - 2 - 2 * x, by omega⟩
  have hc1 : 3 * q - 1 - 2 * x = c + 1 := by omega
  have hc2 : 3 * q - 2 - 2 * x = c := by omega
  obtain ⟨m, hm⟩ : ∃ m, 3 * q = m + 2 := ⟨3 * q - 2, by omega⟩
  have hm2 : 3 * q - 2 = m := by omega
  rw [hc2, hm2]
  have hT : (((3 * q - 2 * x : ℕ) : ℝ)) * (((3 * q - 1 - 2 * x : ℕ) : ℝ)) * T x x (3 * q - 2 * x) =
      T x x c := by
    rw [hc, hc1]
    calc ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) * T x x (c + 2)
        = ((c + 1 : ℕ) : ℝ) * (((c + 1 + 1 : ℕ) : ℝ) * T x x (c + 1 + 1)) := by ring
      _ = ((c + 1 : ℕ) : ℝ) * T x x (c + 1) := by rw [mul_T_thd x x (c + 1)]
      _ = T x x c := mul_T_thd x x c
  have hfact : ((3 * q).factorial : ℝ) = (3 * (q : ℝ)) * (3 * (q : ℝ) - 1) * (m.factorial : ℝ) := by
    rw [hm, Nat.factorial_succ, Nat.factorial_succ]
    have hqR : (m : ℝ) + 2 = 3 * (q : ℝ) := by exact_mod_cast hm.symm
    push_cast
    rw [show (m : ℝ) + 1 + 1 = 3 * (q : ℝ) by linarith,
        show (m : ℝ) + 1 = 3 * (q : ℝ) - 1 by linarith]
    ring
  have hpow : (3 : ℝ) ^ (3 * q) = 9 * (3 : ℝ) ^ m := by
    rw [hm, pow_succ, pow_succ]; ring
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have h3q1 : 3 * (q : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have h3m : (3 : ℝ) ^ m ≠ 0 := by positivity
  calc (m.factorial : ℝ) / (3 : ℝ) ^ m * T x x c
      = (m.factorial : ℝ) / (3 : ℝ) ^ m *
          ((((3 * q - 2 * x : ℕ) : ℝ)) * (((3 * q - 1 - 2 * x : ℕ) : ℝ)) * T x x (3 * q - 2 * x)) := by
        rw [hT]
    _ = (3 * ((3 * q - 2 * x : ℕ) : ℝ) * ((3 * q - 1 - 2 * x : ℕ) : ℝ) /
          ((q : ℝ) * (3 * (q : ℝ) - 1))) *
          (((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q) * T x x (3 * q - 2 * x)) := by
        rw [hfact, hpow]; field_simp; ring

lemma sgnSum_3q_sub_2 (q : ℕ) (hq : 2 ≤ q) :
    ((3 * q - 2).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 2) * sgnSum (3 * q - 2) =
      (3 * (q : ℝ) / (3 * (q : ℝ) - 1)) * p3q q q *
        ((1 - 1 / (q : ℝ)) * (1 + sumA q) - (4 - 2 / (q : ℝ)) * sumB q + 4 * sumC q) := by
  have hp0 : p3q q q ≠ 0 := ne_of_gt (p3q_center_pos q)
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have h3q1 : 3 * (q : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  let α : ℝ := 3 * (q : ℝ) / (3 * (q : ℝ) - 1)
  unfold sumA sumB sumC
  have hrhs : α * p3q q q *
      ((1 - 1 / (q : ℝ)) * (1 + (∑ k ∈ Finset.Icc 1 q, (p3q q (q + k) - p3q q (q - k))) / p3q q q) -
       (4 - 2 / (q : ℝ)) * ((∑ k ∈ Finset.Icc 1 q, ((k : ℝ) / (q : ℝ)) * (p3q q (q + k) + p3q q (q - k))) / p3q q q) +
       4 * ((∑ k ∈ Finset.Icc 1 q, (((k : ℝ) / (q : ℝ)) ^ 2) * (p3q q (q + k) - p3q q (q - k))) / p3q q q)) =
      α * (1 - 1 / (q : ℝ)) * p3q q q +
      ∑ k ∈ Finset.Icc 1 q,
        (α * (1 - 2 * (k : ℝ) / (q : ℝ)) * (1 - 1 / (q : ℝ) - 2 * (k : ℝ) / (q : ℝ)) * p3q q (q + k) -
         α * (1 + 2 * (k : ℝ) / (q : ℝ)) * (1 - 1 / (q : ℝ) + 2 * (k : ℝ) / (q : ℝ)) * p3q q (q - k)) := by
    have hmul : α * p3q q q *
      ((1 - 1 / (q : ℝ)) * (1 + (∑ k ∈ Finset.Icc 1 q, (p3q q (q + k) - p3q q (q - k))) / p3q q q) -
       (4 - 2 / (q : ℝ)) * ((∑ k ∈ Finset.Icc 1 q, ((k : ℝ) / (q : ℝ)) * (p3q q (q + k) + p3q q (q - k))) / p3q q q) +
       4 * ((∑ k ∈ Finset.Icc 1 q, (((k : ℝ) / (q : ℝ)) ^ 2) * (p3q q (q + k) - p3q q (q - k))) / p3q q q)) =
      α * (1 - 1 / (q : ℝ)) * p3q q q +
      (α * (1 - 1 / (q : ℝ)) * ∑ k ∈ Finset.Icc 1 q, (p3q q (q + k) - p3q q (q - k)) -
       α * (4 - 2 / (q : ℝ)) * ∑ k ∈ Finset.Icc 1 q, ((k : ℝ) / (q : ℝ)) * (p3q q (q + k) + p3q q (q - k)) +
       4 * α * ∑ k ∈ Finset.Icc 1 q, (((k : ℝ) / (q : ℝ)) ^ 2) * (p3q q (q + k) - p3q q (q - k))) := by
      field_simp; ring
    rw [hmul]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hrhs]
  unfold sgnSum
  rw [Finset.mul_sum]
  have hq_mem : q ∈ Finset.range ((3 * q - 2) / 2 + 1) := by rw [mem_range]; omega
  have hq_term : ((3 * q - 2).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 2) *
      (if 3 * q > 3 * q - 2 then T q q (3 * q - 2 - 2 * q)
       else if 3 * q < 3 * q - 2 then -T q q (3 * q - 2 - 2 * q) else 0) =
      α * (1 - 1 / (q : ℝ)) * p3q q q := by
    rw [ite_eq_left (by omega), step_3q_sub_2 q q hq (by omega)]
    have h1 : 3 * q - 2 * q = q := by omega
    have h2 : 3 * q - 1 - 2 * q = q - 1 := by omega
    have h3 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [h1, h2, h3]
    dsimp only [α]; field_simp
  rw [← Finset.add_sum_erase _ _ hq_mem, hq_term]
  have hsplit : ∑ x ∈ (Finset.range ((3 * q - 2) / 2 + 1)).erase q,
      ((3 * q - 2).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 2) *
        (if 3 * x > 3 * q - 2 then T x x (3 * q - 2 - 2 * x)
         else if 3 * x < 3 * q - 2 then -T x x (3 * q - 2 - 2 * x) else 0) =
      (∑ x ∈ (Finset.range ((3 * q - 2) / 2 + 1)).filter (fun x => q < x),
        (3 * ((3 * q - 2 * x : ℕ) : ℝ) * ((3 * q - 1 - 2 * x : ℕ) : ℝ) /
          ((q : ℝ) * (3 * (q : ℝ) - 1))) * p3q q x) -
      (∑ x ∈ (Finset.range ((3 * q - 2) / 2 + 1)).filter (fun x => x < q),
        (3 * ((3 * q - 2 * x : ℕ) : ℝ) * ((3 * q - 1 - 2 * x : ℕ) : ℝ) /
          ((q : ℝ) * (3 * (q : ℝ) - 1))) * p3q q x) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    have herase := Finset.add_sum_erase (Finset.range ((3 * q - 2) / 2 + 1))
      (fun x => (if q < x then (3 * ((3 * q - 2 * x : ℕ) : ℝ) * ((3 * q - 1 - 2 * x : ℕ) : ℝ) /
          ((q : ℝ) * (3 * (q : ℝ) - 1))) * p3q q x else 0) -
        (if x < q then (3 * ((3 * q - 2 * x : ℕ) : ℝ) * ((3 * q - 1 - 2 * x : ℕ) : ℝ) /
          ((q : ℝ) * (3 * (q : ℝ) - 1))) * p3q q x else 0)) hq_mem
    simp only [lt_irrefl, ↓reduceIte, sub_self, zero_add] at herase
    rw [← herase]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_erase, mem_range] at hx
    have h2x : 2 * x ≤ 3 * q - 2 := by omega
    by_cases hgt : q < x
    · rw [ite_eq_left (by omega), ite_eq_left hgt, ite_eq_right (by omega), sub_zero]
      exact step_3q_sub_2 q x hq h2x
    · have hlt : x < q := by omega
      rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right hgt, ite_eq_left hlt, zero_sub, mul_neg]
      congr 1
      exact step_3q_sub_2 q x hq h2x
  rw [hsplit, Finset.sum_sub_distrib]
  congr 1
  rw [show (∑ x ∈ (Finset.range ((3 * q - 2) / 2 + 1)).filter (fun x => q < x),
        (3 * ((3 * q - 2 * x : ℕ) : ℝ) * ((3 * q - 1 - 2 * x : ℕ) : ℝ) /
          ((q : ℝ) * (3 * (q : ℝ) - 1))) * p3q q x) =
      ∑ k ∈ Finset.Icc 1 q,
        α * (1 - 2 * (k : ℝ) / (q : ℝ)) * (1 - 1 / (q : ℝ) - 2 * (k : ℝ) / (q : ℝ)) * p3q q (q + k) by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 q) (fun k => 2 * k ≤ q - 2)]
    have hzero : ∑ k ∈ (Finset.Icc 1 q).filter (fun k => ¬ 2 * k ≤ q - 2),
        α * (1 - 2 * (k : ℝ) / (q : ℝ)) * (1 - 1 / (q : ℝ) - 2 * (k : ℝ) / (q : ℝ)) * p3q q (q + k) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [mem_filter, mem_Icc] at hk
      by_cases h1 : 2 * k = q
      · have : 1 - 2 * (k : ℝ) / (q : ℝ) = 0 := by
          have : (2 * k : ℝ) = (q : ℝ) := by exact_mod_cast h1
          field_simp; linarith
        rw [this, mul_zero, zero_mul, zero_mul]
      · by_cases h2 : 2 * k = q - 1
        · have : 1 - 1 / (q : ℝ) - 2 * (k : ℝ) / (q : ℝ) = 0 := by
            have : (2 * k : ℝ) = (q : ℝ) - 1 := by
              have : 2 * k + 1 = q := by omega
              have hR : (2 * k : ℝ) + 1 = (q : ℝ) := by exact_mod_cast this
              linarith
            field_simp; linarith
          rw [this, mul_zero, zero_mul]
        · rw [p3q_eq_zero_of_gt (by omega), mul_zero]
    rw [hzero, add_zero]
    refine Finset.sum_bij (fun x _ => x - q) ?_ ?_ ?_ ?_
    · intro x hx; rw [mem_filter, mem_range] at hx; rw [mem_filter, mem_Icc]; omega
    · intro x1 hx1 x2 hx2 h; rw [mem_filter] at hx1 hx2; omega
    · intro k hk; rw [mem_filter, mem_Icc] at hk
      exact ⟨q + k, by rw [mem_filter, mem_range]; omega, by omega⟩
    · intro x hx
      rw [mem_filter, mem_range] at hx
      have h1 : q + (x - q) = x := by omega
      have h2 : ((3 * q - 2 * x : ℕ) : ℝ) = (q : ℝ) - 2 * ((x - q : ℕ) : ℝ) := by
        have : (3 * q - 2 * x : ℕ) + 2 * (x - q) = q := by omega
        have hR : ((3 * q - 2 * x : ℕ) : ℝ) + 2 * ((x - q : ℕ) : ℝ) = (q : ℝ) := by exact_mod_cast this
        linarith
      have h3 : ((3 * q - 1 - 2 * x : ℕ) : ℝ) = (q : ℝ) - 1 - 2 * ((x - q : ℕ) : ℝ) := by
        have : (3 * q - 1 - 2 * x : ℕ) + 1 + 2 * (x - q) = q := by omega
        have hR : ((3 * q - 1 - 2 * x : ℕ) : ℝ) + 1 + 2 * ((x - q : ℕ) : ℝ) = (q : ℝ) := by exact_mod_cast this
        linarith
      rw [h1, h2, h3]; dsimp only [α]; field_simp]
  congr 1
  refine Finset.sum_bij (fun x _ => q - x) ?_ ?_ ?_ ?_
  · intro x hx; rw [mem_filter, mem_range] at hx; rw [mem_Icc]; omega
  · intro x1 hx1 x2 hx2 h; rw [mem_filter] at hx1 hx2; omega
  · intro k hk; rw [mem_Icc] at hk
    exact ⟨q - k, by rw [mem_filter, mem_range]; omega, by omega⟩
  · intro x hx
    rw [mem_filter, mem_range] at hx
    have h1 : q - (q - x) = x := by omega
    have h2 : ((3 * q - 2 * x : ℕ) : ℝ) = (q : ℝ) + 2 * ((q - x : ℕ) : ℝ) := by
      have : (3 * q - 2 * x : ℕ) = q + 2 * (q - x) := by omega
      exact_mod_cast this
    have h3 : ((3 * q - 1 - 2 * x : ℕ) : ℝ) = (q : ℝ) - 1 + 2 * ((q - x : ℕ) : ℝ) := by
      have : (3 * q - 1 - 2 * x : ℕ) + 1 = q + 2 * (q - x) := by omega
      have hR : ((3 * q - 1 - 2 * x : ℕ) : ℝ) + 1 = (q : ℝ) + 2 * ((q - x : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    rw [h1, h2, h3]; dsimp only [α]; field_simp

/-! ### Part 5: Main exact reduction theorems for all three residue classes -/

/-- Exact 1D reduction for `L = 3q` (`q ≥ 1`). -/
theorem hAdj_mod0 (q : ℕ) (hq : 1 ≤ q) :
    hAdj (3 * q) =
      (3 * (q : ℝ)) / 9 +
      2 * (q : ℝ) * p3q q q * (1 + sumA q - 2 * sumB q) +
      4 * (q : ℝ) ^ 2 * p3q q q := by
  rw [hAdj_eq_sgnSum (3 * q) (by omega)]
  have hdiv : (3 * q - 1) / 3 = q - 1 := by omega
  have hPhi : PhiNat (3 * q) ((3 * q - 1) / 3 + 1) = (q : ℝ) ^ 2 * T q q q := by
    rw [hdiv]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have hmod : (3 * (q' + 1) - q') % 2 = 1 := by omega
    have hB : (3 * (q' + 1) - q' - 1) / 2 = q' + 1 := by omega
    simp only [PhiNat, hmod, one_ne_zero, ↓reduceIte, hB, Nat.add_sub_cancel]
    have ha := mul_T_fst q' (q' + 1) (q' + 1)
    have hb := mul_T_snd q' q' (q' + 1)
    calc T q' q' (q' + 1) = ((q' + 1 : ℕ) : ℝ) * T q' (q' + 1) (q' + 1) := hb.symm
      _ = ((q' + 1 : ℕ) : ℝ) * (((q' + 1 : ℕ) : ℝ) * T (q' + 1) (q' + 1) (q' + 1)) := by rw [ha]
      _ = ((q' + 1 : ℕ) : ℝ) ^ 2 * T (q' + 1) (q' + 1) (q' + 1) := by ring
  rw [hPhi, ite_eq_right (by omega), ite_eq_right (by omega), add_zero, add_zero]
  have hsgn := sgnSum_3q_sub_1 q hq
  have hp0 : p3q q q = ((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q) * T q q q := by
    rw [p3q_eq_of_le (by omega)]
    have : 3 * q - 2 * q = q := by omega
    rw [this]
  obtain ⟨m, hm⟩ : ∃ m, 3 * q = m + 1 := ⟨3 * q - 1, by omega⟩
  have hm' : 3 * q - 1 = m := by omega
  have hfac : ((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q) =
      (q : ℝ) * ((m.factorial : ℝ) / (3 : ℝ) ^ m) := by
    rw [hm, Nat.factorial_succ, pow_succ]
    have hmR : (m : ℝ) + 1 = 3 * (q : ℝ) := by exact_mod_cast hm.symm
    have h3 : (3 : ℝ) ^ m ≠ 0 := by positivity
    push_cast; field_simp; linarith
  rw [hm'] at hsgn
  have hterm2 : 2 * (((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q)) * sgnSum m =
      2 * (q : ℝ) * p3q q q * (1 + sumA q - 2 * sumB q) := by
    rw [hfac, show 2 * ((q : ℝ) * ((m.factorial : ℝ) / (3 : ℝ) ^ m)) * sgnSum m =
      2 * (q : ℝ) * ((m.factorial : ℝ) / (3 : ℝ) ^ m * sgnSum m) by ring, hsgn]
    ring
  have hterm3 : 4 * (((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q)) * ((q : ℝ) ^ 2 * T q q q) =
      4 * (q : ℝ) ^ 2 * p3q q q := by
    rw [hp0]; ring
  rw [hm', hterm2, hterm3]
  push_cast; ring

/-- Exact 1D reduction for `L = 3q + 1` (`q ≥ 1`). -/
theorem hAdj_mod1 (q : ℕ) (hq : 1 ≤ q) :
    hAdj (3 * q + 1) =
      (3 * (q : ℝ) + 1) / 9 +
      (2 * (3 * (q : ℝ) + 1) / 3) * p3q q q * sumA q +
      (2 * (6 * (q : ℝ) + 1) * (3 * (q : ℝ) + 1) / 9) * p3q q q := by
  rw [hAdj_eq_sgnSum (3 * q + 1) (by omega)]
  rw [Nat.add_sub_cancel]
  have hmod : (3 * q) % 3 = 0 := by omega
  have hdiv : (3 * q) / 3 = q := by omega
  have hPhi : PhiNat (3 * q + 1) ((3 * q) / 3 + 1) = (q : ℝ) * T q q q := by
    rw [hdiv]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hmod2 : (3 * (q' + 1) + 1 - (q' + 1)) % 2 = 1 := by omega
    have hB : (3 * (q' + 1) + 1 - (q' + 1) - 1) / 2 = q' + 1 := by omega
    simp only [PhiNat, hmod2, one_ne_zero, ↓reduceIte, hB, Nat.add_sub_cancel]
    exact (mul_T_snd (q' + 1) q' (q' + 1)).symm
  rw [hPhi, ite_eq_right (by omega), ite_eq_left hmod, hdiv, add_zero]
  have hp0 : p3q q q = ((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q) * T q q q := by
    rw [p3q_eq_of_le (by omega)]
    have : 3 * q - 2 * q = q := by omega
    rw [this]
  have hfac : ((3 * q + 1).factorial : ℝ) / (3 : ℝ) ^ (3 * q + 1) =
      ((3 * (q : ℝ) + 1) / 3) * (((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q)) := by
    rw [Nat.factorial_succ, pow_succ]
    have h3 : (3 : ℝ) ^ (3 * q) ≠ 0 := by positivity
    push_cast; field_simp
  rw [hfac]
  have hsgn := sgnSum_3q q
  have hterm2 : 2 * (((3 * (q : ℝ) + 1) / 3) * (((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q))) * sgnSum (3 * q) =
      (2 * (3 * (q : ℝ) + 1) / 3) * p3q q q * sumA q := by
    rw [show 2 * (((3 * (q : ℝ) + 1) / 3) * (((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q))) * sgnSum (3 * q) =
      (2 * (3 * (q : ℝ) + 1) / 3) * (((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q) * sgnSum (3 * q)) by ring, hsgn]
    ring
  have hterm3 : 4 * (((3 * (q : ℝ) + 1) / 3) * (((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q))) *
      ((q : ℝ) * T q q q + (1 / 6 : ℝ) * T q q q) =
      (2 * (6 * (q : ℝ) + 1) * (3 * (q : ℝ) + 1) / 9) * p3q q q := by
    rw [hp0]; ring
  rw [hterm2, hterm3]
  push_cast; ring

/-- Exact 1D reduction for `L = 3q - 1` (`q ≥ 2`). -/
theorem hAdj_mod2 (q : ℕ) (hq : 2 ≤ q) :
    hAdj (3 * q - 1) =
      (3 * (q : ℝ) - 1) / 9 +
      2 * (q : ℝ) * p3q q q *
        ((1 - 1 / (q : ℝ)) * (1 + sumA q) - (4 - 2 / (q : ℝ)) * sumB q + 4 * sumC q) +
      4 * (q : ℝ) ^ 2 * p3q q q := by
  rw [hAdj_eq_sgnSum (3 * q - 1) (by omega)]
  have hm : 3 * q - 1 - 1 = 3 * q - 2 := by omega
  rw [hm]
  have hmod1 : (3 * q - 2) % 3 = 1 := by omega
  have hdiv1 : (3 * q - 2) / 3 = q - 1 := by omega
  have hdiv2 : (3 * q - 1 - 2) / 3 = q - 1 := by omega
  have hPhi : PhiNat (3 * q - 1) ((3 * q - 2) / 3 + 1) +
      T ((3 * q - 1 - 2) / 3) ((3 * q - 1 - 2) / 3) ((3 * q - 1 - 2) / 3 + 1) =
      T (q - 1) (q - 1) (q - 1) := by
    rw [hdiv1, hdiv2]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
    have hq1 : q' + 2 - 1 = q' + 1 := by omega
    rw [hq1]
    have hmod2 : (3 * (q' + 2) - 1 - (q' + 1)) % 2 = 0 := by omega
    have hdivM : (3 * (q' + 2) - 1 - (q' + 1)) / 2 = q' + 2 := by omega
    simp only [PhiNat, hmod2, ↓reduceIte, hdivM]
    have hsub : q' + 2 - 2 = q' := by omega
    rw [hsub]
    have h1 := mul_T_thd (q' + 1) (q' + 1) (q' + 1)
    have h2 := mul_T_snd (q' + 1) q' (q' + 2)
    have hsum : ((q' + 1 : ℕ) : ℝ) * T (q' + 1) (q' + 1) (q' + 2) +
        T (q' + 1) (q' + 1) (q' + 2) = ((q' + 2 : ℕ) : ℝ) * T (q' + 1) (q' + 1) (q' + 2) := by
      push_cast; ring
    linarith
  rw [ite_eq_left hmod1, ite_eq_right (by omega), add_zero, hPhi]
  have hsgn := sgnSum_3q_sub_2 q hq
  have hp0 : p3q q q = ((3 * q).factorial : ℝ) / (3 : ℝ) ^ (3 * q) * T q q q := by
    rw [p3q_eq_of_le (by omega)]
    have : 3 * q - 2 * q = q := by omega
    rw [this]
  have h3q1 : 3 * (q : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  obtain ⟨m2, hm2⟩ : ∃ m2, 3 * q = m2 + 2 := ⟨3 * q - 2, by omega⟩
  have hm2' : 3 * q - 2 = m2 := by omega
  have hm1' : 3 * q - 1 = m2 + 1 := by omega
  have hfac1 : ((3 * q - 1).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 1) =
      ((3 * (q : ℝ) - 1) / 3) * (((3 * q - 2).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 2)) := by
    rw [hm1', hm2', Nat.factorial_succ, pow_succ]
    have hmR : (m2 : ℝ) + 1 = 3 * (q : ℝ) - 1 := by
      have : (m2 : ℝ) + 2 = 3 * (q : ℝ) := by exact_mod_cast hm2.symm
      linarith
    have h3 : (3 : ℝ) ^ m2 ≠ 0 := by positivity
    push_cast; field_simp; linarith
  have hfac2 : ((3 * q - 1).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 1) * T (q - 1) (q - 1) (q - 1) =
      (q : ℝ) ^ 2 * p3q q q := by
    rw [hp0]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have hT3 : ((q' + 1 : ℕ) : ℝ) ^ 3 * T (q' + 1) (q' + 1) (q' + 1) = T q' q' q' := by
      have h1 := mul_T_fst q' (q' + 1) (q' + 1)
      have h2 := mul_T_snd q' q' (q' + 1)
      have h3 := mul_T_thd q' q' q'
      calc ((q' + 1 : ℕ) : ℝ) ^ 3 * T (q' + 1) (q' + 1) (q' + 1)
          = ((q' + 1 : ℕ) : ℝ) * (((q' + 1 : ℕ) : ℝ) * (((q' + 1 : ℕ) : ℝ) * T (q' + 1) (q' + 1) (q' + 1))) := by ring
        _ = ((q' + 1 : ℕ) : ℝ) * (((q' + 1 : ℕ) : ℝ) * T q' (q' + 1) (q' + 1)) := by rw [h1]
        _ = ((q' + 1 : ℕ) : ℝ) * T q' q' (q' + 1) := by rw [h2]
        _ = T q' q' q' := h3
    obtain ⟨m, hm_eq⟩ : ∃ m, 3 * (q' + 1) = m + 1 := ⟨3 * (q' + 1) - 1, by omega⟩
    have hm_sub : 3 * (q' + 1) - 1 = m := by omega
    rw [hm_sub, ← hT3]
    have hfact3 : ((3 * (q' + 1)).factorial : ℝ) = (3 * ((q' + 1 : ℕ) : ℝ)) * (m.factorial : ℝ) := by
      rw [hm_eq, Nat.factorial_succ]
      have hmR : (m : ℝ) + 1 = 3 * ((q' + 1 : ℕ) : ℝ) := by exact_mod_cast hm_eq.symm
      push_cast
      rw [show (m : ℝ) + 1 = 3 * ((q' : ℝ) + 1) by push_cast at hmR; linarith]
    have hpow3 : (3 : ℝ) ^ (3 * (q' + 1)) = 3 * (3 : ℝ) ^ m := by
      rw [hm_eq, pow_succ]; ring
    rw [hfact3, hpow3]
    have h3 : (3 : ℝ) ^ m ≠ 0 := by positivity
    have hq' : ((q' + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast; field_simp
  have hcastL : ((3 * q - 1 : ℕ) : ℝ) = 3 * (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcastL]
  have hterm2 : 2 * (((3 * q - 1).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 1)) * sgnSum (3 * q - 2) =
      2 * (q : ℝ) * p3q q q *
        ((1 - 1 / (q : ℝ)) * (1 + sumA q) - (4 - 2 / (q : ℝ)) * sumB q + 4 * sumC q) := by
    rw [hfac1, show 2 * (((3 * (q : ℝ) - 1) / 3) * (((3 * q - 2).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 2))) *
      sgnSum (3 * q - 2) =
      (2 * (3 * (q : ℝ) - 1) / 3) * (((3 * q - 2).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 2) * sgnSum (3 * q - 2)) by ring,
      hsgn]
    field_simp
  have hterm3 : 4 * (((3 * q - 1).factorial : ℝ) / (3 : ℝ) ^ (3 * q - 1)) * T (q - 1) (q - 1) (q - 1) =
      4 * (q : ℝ) ^ 2 * p3q q q := by
    rw [mul_assoc, hfac2]; ring
  rw [hterm2, hterm3]

end MultinomialTV
