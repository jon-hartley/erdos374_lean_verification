import Item1GrowthToZeroFree
import Item1ZeroFreeSourceEndpoint

/-! UNCOMPILED final insertion. The left-of-one logarithmic modulus estimate
is the one genuine unproved arithmetic premise of this concluding type.
The theorem does not prove that estimate, Item 2, or an unconditional endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Filter MeasureTheory Set
namespace Item1GrowthSourceEndpoint
open Item1GrowthToZeroFree CancellationTransferCenter

theorem literal_item1_of_left_log_growth (A : ℕ) (C Tg : ℝ)
    (hC : 1≤C) (hg : LeftLogarithmicZetaGrowth A C Tg) :
    ∀ᶠ X : ℝ in atTop,
      (∫ x in Icc X (2*X), sourceResidualAbs X x
        (x*(X^((101:ℝ)/1000)/2)/X))/X ≤ 1/(Real.log X)^2 := by
  obtain ⟨T,hT,hzero⟩ := bare_zero_free_of_left_growth A C Tg hC hg
  exact Item1ZeroFreeSourceEndpoint.literal_item1_of_bare_zero_free
    (1/20) T (by norm_num) (by norm_num) hT hzero

end Item1GrowthSourceEndpoint

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1GrowthSourceEndpoint.literal_item1_of_left_log_growth] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1GrowthSourceEndpoint: 1 original theorem guards passed."
