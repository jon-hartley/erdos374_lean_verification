import Item1PhaseZeroFreeEndpoint
import Item1GrowthSourceEndpoint

/-! UNCOMPILED integration. The first premise below is still an UNPROVED
finite exponential-sum statement. This file does not close Item 1. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set
namespace Item1IntermediatePhaseEndpoint
open Item1DyadicPhaseReduction Item1PhaseZetaGrowth Item1GrowthToZeroFree

/-- A conditional source endpoint. A clean axiom list here would NOT prove hcore. -/
theorem literal_item1_of_intermediate_phase (T : ℝ) (hcore : IntermediatePhaseInput T) :
    ∀ᶠ X : ℝ in atTop,
      (∫ x in Icc X (2*X), CancellationTransferCenter.sourceResidualAbs X x
        (x*(X^((101:ℝ)/1000)/2)/X))/X≤1/(Real.log X)^2 := by
  exact Item1GrowthSourceEndpoint.literal_item1_of_left_log_growth 7 128
    (max T (Real.exp 8)) (by norm_num) (left_growth_of_intermediate_phase T hcore)

end Item1IntermediatePhaseEndpoint

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1IntermediatePhaseEndpoint.literal_item1_of_intermediate_phase] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1IntermediatePhaseEndpoint: 1 original theorem guards passed."
