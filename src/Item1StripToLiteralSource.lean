import Item1SharpCapFromStrip
import Item1RetainedMomentEndpoint

/-!
UNCOMPILED integration against the ACTUAL retained project definitions.
The exact dyadic polynomial is identified term-by-term before the cap is
inserted. PositiveStrip is still a genuine, unproved hypothesis. This is not
an unconditional Item 1 or Item 2 theorem. No project definitions are changed.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Filter MeasureTheory Set
namespace Item1StripToLiteralSource
open Item1SharpDyadicSmoothing Item1SharpCapFromStrip Item1ZetaContourGeometry
open Item1RetainedPolynomialCap Item1RetainedMomentEndpoint
open Item1ExactFirstBlock Erdos374.HarmanGram152 SourceMassDischarge
open CancellationTransferCenter

/-- Match exponential and complex-power conventions on the positive original Ico support. -/
theorem dyadic_eq_original_block (N : ℕ) (hN : 1≤N) (t : ℝ) :
    dyadic N t = Item1ExactFirstBlock.block N t := by
  unfold dyadic Item1ExactFirstBlock.block verticalDirichlet152
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : (0:ℝ)<n := by
    exact_mod_cast (show 0<n from lt_of_lt_of_le (by omega) (Finset.mem_Ico.mp hn).1)
  unfold term mangoldt
  have hpow : (n:ℂ)^(-((1:ℂ)+Complex.I*(t:ℂ))) =
      Complex.exp (-((1:ℂ)+Complex.I*(t:ℂ))*(Real.log (n:ℝ):ℂ)) := by
    simpa only [Complex.ofReal_natCast] using
      Item1RampDirichlet.cpow_positive_exp (n:ℝ) hnp (-((1:ℂ)+Complex.I*(t:ℂ)))
  simp only [Complex.ofReal_one]
  rw [hpow]
  congr 2
  ring

/-- Construct the parent's cap input. No polynomial-cap premise remains here. -/
theorem polynomial_input_of_positive_strip (a C T₀ : ℝ)
    (ha : 0<a) (ha1 : a≤1/2) (hC : 0<C) (hT : 4≤T₀)
    (hs : PositiveStrip a C T₀) : PolynomialHeightInput := by
  obtain ⟨N₀,hN₀,hcap⟩ := sharp_cap_26001 a C T₀ ha ha1 hC hT hs
  refine ⟨52008,1,N₀,by norm_num,hN₀,?_⟩
  intro N hN t _ht htlo hthi
  have hh := hcap N hN t htlo hthi
  simpa only [dyadic_eq_original_block N (by omega) t] using hh

/-- Connected conditional Item 1: no cap, middle, energy or deletion budget argument.
The remaining analytic premise is the explicitly displayed genuine zeta strip. -/
theorem literal_item1_of_positive_strip (a C T₀ : ℝ)
    (ha : 0<a) (ha1 : a≤1/2) (hC : 0<C) (hT : 4≤T₀)
    (hs : PositiveStrip a C T₀) :
    ∀ᶠ X : ℝ in atTop,
      (∫ x in Icc X (2*X), sourceResidualAbs X x
        (x*(X^((101:ℝ)/1000)/2)/X))/X ≤ 1/(Real.log X)^2 := by
  exact Item1RetainedMomentEndpoint.literal_item1_explicit_width
    (polynomial_input_of_positive_strip a C T₀ ha ha1 hC hT hs)

end Item1StripToLiteralSource

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1StripToLiteralSource.dyadic_eq_original_block,
    ``Item1StripToLiteralSource.polynomial_input_of_positive_strip,
    ``Item1StripToLiteralSource.literal_item1_of_positive_strip] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1StripToLiteralSource: 3 original theorem guards passed."
