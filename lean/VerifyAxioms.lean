/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public meta import Lean
import all MultinomialTVConjecture.Combinatorial
import all MultinomialTVConjecture.StirlingRefined
import all MultinomialTVConjecture.GaussianEulerMaclaurin
import all MultinomialTVConjecture.LocalAsymptotics
import all MultinomialTVConjecture.Main
import all MultinomialTVConjecture.NonVacuity
import all MultinomialTVConjecture
import all Solution

/-!
# Exhaustive Axiom Audit for Multinomial TV Conjecture (Conjecture 7.7)

Prints `#print axioms` for:
  - All 27 primary theorems in `MultinomialTV`
  - All 22 non-vacuity and adversarial-refutation theorems in `MultinomialTV.NonVacuity`
  - All 10 isolated comparator target theorems in `MultinomialTV.ComparatorTarget`
PLUS runs an exhaustive `Lean.collectAxioms` metaprogram auditing EVERY `theorem` AND EVERY
`def` declaration across the entire `MultinomialTV` namespace tree and private proof modules.

Run: `cd lean && lake env lean VerifyAxioms.lean`
Every theorem and definition must depend strictly on `[propext, Classical.choice, Quot.sound]` (or fewer).
-/

-- Primary exported theorems (27 declarations)
#print axioms MultinomialTV.hAdj_eq_nested_sum
#print axioms MultinomialTV.hAdj_mod0
#print axioms MultinomialTV.hAdj_mod1
#print axioms MultinomialTV.hAdj_mod2
#print axioms MultinomialTV.p3q_center_expansion
#print axioms MultinomialTV.oddGauss_sum_approx
#print axioms MultinomialTV.oddGauss_sum_approx_order4
#print axioms MultinomialTV.tendsto_sumA
#print axioms MultinomialTV.tendsto_sumB
#print axioms MultinomialTV.tendsto_sumC
#print axioms MultinomialTV.sumA_O_inv_sq
#print axioms MultinomialTV.sumB_O_inv_sq
#print axioms MultinomialTV.sumC_O_inv_sq
#print axioms MultinomialTV.tendsto_hAdj_mod0
#print axioms MultinomialTV.tendsto_hAdj_mod1
#print axioms MultinomialTV.tendsto_hAdj_mod2
#print axioms MultinomialTV.lemma_7_3_O_inv_sq
#print axioms MultinomialTV.conjecture_7_7_aTriangle
#print axioms MultinomialTV.conjecture_7_7_gamma2
#print axioms MultinomialTV.conjecture_7_7_d0
#print axioms MultinomialTV.bRes_cosine_formula
#print axioms MultinomialTV.conjecture_7_7
#print axioms MultinomialTV.gamma_closed_form
#print axioms MultinomialTV.gamma_cyclic_closed_form
#print axioms MultinomialTV.gamma3_closed_form
#print axioms MultinomialTV.gamma3_source_form
#print axioms MultinomialTV.gamma4_closed_form

-- Non-vacuity witnesses and adversarial definition checks (22 declarations)
#print axioms MultinomialTV.NonVacuity.hAdj_zero
#print axioms MultinomialTV.NonVacuity.hAdj_one
#print axioms MultinomialTV.NonVacuity.hAdj_two
#print axioms MultinomialTV.NonVacuity.hAdj_three
#print axioms MultinomialTV.NonVacuity.hAdj_four
#print axioms MultinomialTV.NonVacuity.hAdj_five
#print axioms MultinomialTV.NonVacuity.bRes_zero_pos
#print axioms MultinomialTV.NonVacuity.bRes_one_neg
#print axioms MultinomialTV.NonVacuity.bRes_zero_ne_one
#print axioms MultinomialTV.NonVacuity.d0_neg
#print axioms MultinomialTV.NonVacuity.aTriangle_lt_one_div_32
#print axioms MultinomialTV.NonVacuity.aTriangle_pos
#print axioms MultinomialTV.NonVacuity.gamma2_neg
#print axioms MultinomialTV.NonVacuity.adversarial_aTriangle_ne_one_div_32
#print axioms MultinomialTV.NonVacuity.adversarial_d0_ne_zero
#print axioms MultinomialTV.NonVacuity.adversarial_residue_limits_not_constant
#print axioms MultinomialTV.NonVacuity.gamma_closed_form_witness_n5
#print axioms MultinomialTV.NonVacuity.gamma_cyclic_closed_form_witness_n5
#print axioms MultinomialTV.NonVacuity.gamma3_closed_form_witness_N0
#print axioms MultinomialTV.NonVacuity.gamma4_closed_form_witness_N0
#print axioms MultinomialTV.NonVacuity.adversarial_lemma_7_3_zero_const_false
#print axioms MultinomialTV.NonVacuity.gamma3_source_form_witness_N1

-- Isolated Mathlib-only Comparator solution bridge (10 declarations)
#print axioms MultinomialTV.ComparatorTarget.target_tendsto_hAdj_mod0
#print axioms MultinomialTV.ComparatorTarget.target_tendsto_hAdj_mod1
#print axioms MultinomialTV.ComparatorTarget.target_tendsto_hAdj_mod2
#print axioms MultinomialTV.ComparatorTarget.target_conjecture_7_7
#print axioms MultinomialTV.ComparatorTarget.target_gamma_closed_form
#print axioms MultinomialTV.ComparatorTarget.target_gamma_cyclic_closed_form
#print axioms MultinomialTV.ComparatorTarget.target_gamma3_closed_form
#print axioms MultinomialTV.ComparatorTarget.target_gamma4_closed_form
#print axioms MultinomialTV.ComparatorTarget.target_lemma_7_3_O_inv_sq
#print axioms MultinomialTV.ComparatorTarget.target_gamma3_source_form

-- Exhaustive Metaprogram Audit: EVERY named & module-private theorem AND definition across all project modules
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes : Array Name :=
    #[`MultinomialTV, `_private.MultinomialTVConjecture, `_private.Solution]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let allThms := env.constants.toList.filter fun (name, info) =>
    info.isTheorem && prefixes.any (fun p => p.isPrefixOf name)
  let allDefs := env.constants.toList.filter fun (name, info) =>
    info.isDef && prefixes.any (fun p => p.isPrefixOf name)
  if allThms.isEmpty then
    throwError "No project theorems found for exhaustive axiom audit"
  if allDefs.isEmpty then
    throwError "No project definitions found for exhaustive axiom audit"
  let mut bad : Array String := #[]
  for (name, _) in allThms ++ allDefs do
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun a => !allowed.contains a
    if !forbidden.isEmpty then
      bad := bad.push s!"{name}: {forbidden}"
  if !bad.isEmpty then
    throwError s!"Disallowed axioms detected across project declarations:\n{String.intercalate "\n" bad.toList}"
  logInfo m!"ALL_THEOREMS_AXIOM_AUDIT_PASS: checked {allThms.length} theorems and {allDefs.length} definitions across MultinomialTV — 0 disallowed axioms."
