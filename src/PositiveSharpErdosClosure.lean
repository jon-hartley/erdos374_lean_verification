import PositiveSharpErdosReduction
import CheckedSamplingMangoldtCancellation

/-! The sampling premise is discharged by the freshly checked cancellation
chain. The literal residual and signed-remainder moment estimates remain
the two explicit analytic premises of the final factorial conclusion. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set

namespace PositiveSharpErdosClosure
open PositiveSharpPowerWindow PositiveSharpResidual PositiveSharpBoxedCount

theorem polynomial_sampling :
    Erdos374.SamplingPolynomial149.PolynomialReciprocalPrimeSampling :=
  Erdos374.FourierLargePhase151.polynomial_sampling_of_large_phase
    MangoldtCancellation.largePhaseCharacterSampling

theorem eventually_erdos_conclusions_of_means :
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀ s : ℝ, 0<s → s<s₀ →
      ∀ C_E C_R : ℝ,
      (∀ᶠ X : ℝ in atTop,
        (∫ x in Icc X (2*X), residualAbs X x (x*halfWidth X (101/1000)/X))/X≤
          C_E/(Real.log X)^2) →
      (∀ᶠ X : ℝ in atTop,
        (∫ x in Icc X (2*X),
          (signedRemainder X s x (x*halfWidth X (101/1000)/X))^2)/X≤
          C_R*(halfWidth X (101/1000))^2/(Real.log X)^4) →
      Erdos374.MainStatement ∧
      Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
      ∃ c : ℝ, 0<c ∧ ∃ cutoff : ℕ, ∀ N : ℕ, cutoff≤N →
        c*(N:ℝ)≤(Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  obtain ⟨s₀,hs₀,hs1,hb⟩ :=
    PositiveSharpErdosReduction.eventually_erdos_conclusions_of_means_and_sampling
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss C_E C_R hE hR
  exact hb s hs hss C_E C_R hE hR polynomial_sampling

run_cmd do
  for decl in [``polynomial_sampling, ``eventually_erdos_conclusions_of_means] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SAMPLING DISCHARGED; ERDOS CONCLUSION RETAINS EXACTLY TWO LITERAL MOMENT PREMISES"
end PositiveSharpErdosClosure
end
