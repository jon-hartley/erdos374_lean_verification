import Item1ZeroFreeToStrip
import Item1StripToLiteralSource

/-! UNCOMPILED. The input below is BARE ZETA NONVANISHING and remains
unproved. This is a conditional Item 1 implication, not its completion.
No retained source, physical width, full-Mangoldt center or Item 2 is changed. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Filter MeasureTheory Set
namespace Item1ZeroFreeSourceEndpoint
open Item1ZetaDiskGeometry Item1ZeroFreeToStrip CancellationTransferCenter

theorem literal_item1_of_bare_zero_free (b T₀ : ℝ)
    (hb : 0<b) (hb1 : b≤1/2) (hT : 4≤T₀)
    (hzero : BarePositiveZeroFree b T₀) :
    ∀ᶠ X : ℝ in atTop,
      (∫ x in Icc X (2*X), sourceResidualAbs X x
        (x*(X^((101:ℝ)/1000)/2)/X))/X ≤ 1/(Real.log X)^2 := by
  obtain ⟨T₁,hT₁,hstrip⟩ := positiveStrip_of_bare_zero_free b T₀ hb hb1 hT hzero
  exact Item1StripToLiteralSource.literal_item1_of_positive_strip
    (b/8) (3072/b^2) T₁ (by positivity) (by linarith)
    (by positivity) hT₁ hstrip

end Item1ZeroFreeSourceEndpoint

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1ZeroFreeSourceEndpoint.literal_item1_of_bare_zero_free] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1ZeroFreeSourceEndpoint: 1 original theorem guards passed."
