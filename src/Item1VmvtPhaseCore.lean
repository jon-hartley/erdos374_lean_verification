/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Item1PhasePerturbation
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Salt.ExpSum

open Finset
open scoped ComplexConjugate

/-- The normalized additive character `e(x) = exp(2πix)`. -/
noncomputable def eR (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

@[simp] lemma norm_eR (x : ℝ) : ‖eR x‖ = 1 := by
  have h : eR x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    rw [eR]; congr 1; push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma eR_add (x y : ℝ) : eR (x + y) = eR x * eR y := by
  rw [eR, eR, eR, ← Complex.exp_add]; congr 1; push_cast; ring

lemma eR_neg (x : ℝ) : eR (-x) = (eR x)⁻¹ := by
  rw [eR, eR, ← Complex.exp_neg]; congr 1; push_cast; ring

lemma conj_eR (x : ℝ) : conj (eR x) = eR (-x) := by
  rw [eR_neg]; exact (Complex.inv_eq_conj (norm_eR x)).symm

/-- The differencing identity: `eR x · conj (eR y) = eR (x - y)`. -/
lemma eR_mul_conj (x y : ℝ) : eR x * conj (eR y) = eR (x - y) := by
  rw [conj_eR, ← eR_add, ← sub_eq_add_neg]


end Salt.ExpSum

run_cmd do
  for target in [
      ``Salt.ExpSum.norm_eR,
      ``Salt.ExpSum.eR_add,
      ``Salt.ExpSum.eR_neg,
      ``Salt.ExpSum.conj_eR,
      ``Salt.ExpSum.eR_mul_conj] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "VMVT PHASECORE: 5 standard-axiom theorem guards passed."
