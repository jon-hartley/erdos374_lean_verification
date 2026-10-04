import Item1RetainedPolynomialCap

/-! UNCOMPILED. Complete proposed cap-to-middle-to-physical invocation using
ONLY recovered source bodies. PolynomialHeightInput is still an explicit,
unproved arithmetic premise. No unconditional Item 1 or Item 2 is asserted.
-/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Set
namespace Item1RetainedMomentEndpoint
open Item1RetainedPolynomialCap Item1RetainedMomentMiddle
open Item1AllFrequencyMerge Item1TailScalarMerge CancellationTransferCenter

/-- MiddleBudget is constructed, not supplied by the caller. -/
theorem literal_item1_of_polynomial_input (hinput : PolynomialHeightInput) :
    ∀ᶠ X : ℝ in atTop,
      (∫ x in Icc X (2*X), sourceResidualAbs X x (x*width X/X))/X ≤
        1/(Real.log X)^2 := by
  obtain ⟨K,hK,hcap⟩ := eventually_strong_first_cap hinput
  exact item1_of_prime_middle K hK (prime_middle_budget_of_cap K hcap)

/-- The exact maintained half-width is displayed in the resulting theorem type. -/
theorem literal_item1_explicit_width (hinput : PolynomialHeightInput) :
    ∀ᶠ X : ℝ in atTop,
      (∫ x in Icc X (2*X), sourceResidualAbs X x
        (x*(X^((101:ℝ)/1000)/2)/X))/X ≤ 1/(Real.log X)^2 := by
  simpa only [width] using literal_item1_of_polynomial_input hinput

end Item1RetainedMomentEndpoint

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1RetainedMomentEndpoint.literal_item1_of_polynomial_input,
    ``Item1RetainedMomentEndpoint.literal_item1_explicit_width] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1RetainedMomentEndpoint: 2 original theorem guards passed."
