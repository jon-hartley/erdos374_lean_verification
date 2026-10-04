/-
Copyright (c) 2026 Salt contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Item1VmvtPrimeEff

/-! The original weaker prime-count contract, deduced from the effective
elementary estimate with constant 1/8. -/
set_option autoImplicit false

namespace Salt.Vmvt

theorem primes_in_Ioc_ge :
    ∃ c : ℝ, 0 < c ∧ ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      (c * y / Real.log y) ≤ (((Finset.Ioc y (2 * y)).filter Nat.Prime).card : ℝ) := by
  obtain ⟨y₀, _, hcount⟩ := primes_in_Ioc_eff
  refine ⟨1 / 8, by norm_num, y₀, fun y hy => ?_⟩
  convert hcount y hy using 1 <;> ring

end Salt.Vmvt

run_cmd do
  for ax in (← Lean.collectAxioms ``Salt.Vmvt.primes_in_Ioc_ge) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in Salt.Vmvt.primes_in_Ioc_ge"
  Lean.logInfo "VMVT PRIME COUNT: 1 standard-axiom theorem guard passed."
