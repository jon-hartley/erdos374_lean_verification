import Item1LogRampSmoothing
import Item1ZetaDirichletSeries

/-! Exact original sum definitions, separated from the Mellin identity.
No estimate or new hypothesis is introduced. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Item1RampDirichlet
open Item1LogRampSmoothing

def position (N : ℝ) (n : ℕ) : ℝ := Real.log (n+1:ℕ)-Real.log N

def coefficient (t : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt (n+1):ℂ)*
    Complex.exp (-((1:ℂ)+(t:ℂ)*Complex.I)*(Real.log (n+1:ℕ):ℂ))

def smoothSeries (N δ t : ℝ) : ℂ :=
  ∑' n : ℕ, coefficient t n * (weight (Real.log 2) δ (position N n):ℂ)

def smoothFinite (N δ t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (Nat.ceil (4*N)),
    coefficient t n * (weight (Real.log 2) δ (position N n):ℂ)

end Item1RampDirichlet

run_cmd do
  for target in [``Item1RampDirichlet.position, ``Item1RampDirichlet.coefficient,
      ``Item1RampDirichlet.smoothSeries, ``Item1RampDirichlet.smoothFinite] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "RAMP SUM DEFINITIONS PASSED: four original definitions."
