import Mathlib.Basic.Complex.Basic

/-! Exact original line definition, separated from the inversion proof. -/
set_option autoImplicit false
noncomputable section
namespace Item1RampMellinInversion

def line (c v : ℝ) : ℂ := (c:ℂ)+(v:ℂ)*Complex.I

end Item1RampMellinInversion

run_cmd do
  for ax in (← Lean.collectAxioms ``Item1RampMellinInversion.line) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in Item1RampMellinInversion.line"

#print axioms Item1RampMellinInversion.line
