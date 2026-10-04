/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! The elementary logarithm estimate used by the VMVT prime-count proof.
Extracted from Salt.SW.SiegelClose under a local namespace. -/
set_option autoImplicit false

namespace Item1VmvtSupport

/-- `log x ≤ 2√x` for `x > 0`. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hsx
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  linarith

end Item1VmvtSupport

run_cmd do
  for ax in (← Lean.collectAxioms ``Item1VmvtSupport.log_le_two_sqrt) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in Item1VmvtSupport.log_le_two_sqrt"
  Lean.logInfo "VMVT SUPPORT: 1 standard-axiom theorem guard passed."
