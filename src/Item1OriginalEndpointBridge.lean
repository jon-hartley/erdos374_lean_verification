import Item1ParameterEndpoint
import ShortSingletonClosure

/-! Supply the now-proved literal Item 1 mean to the original conditional
Erdos endpoint. The original Item 2 rest-negative-mean premise remains explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set

namespace Item1OriginalEndpointBridge
open CancellationTransferCenter PositiveSharpPowerWindow ShortSingletonClosure

theorem original_source_mean :
    ∀ᶠ X : ℝ in atTop,
      (∫ x in Icc X (2*X), sourceResidualAbs X x
        (x*halfWidth X (101/1000)/X))/X ≤ 1/(Real.log X)^2 := by
  simpa only [halfWidth] using Item1ParameterEndpoint.literal_item1_unconditional

/-- The original endpoint with Item 1 discharged and only Item 2 retained. -/
theorem eventually_erdos_conclusions_of_rest_negative_mean :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/1000 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∀ C_R : ℝ,
      (∀ᶠ X : ℝ in atTop,
        restNegativeMean X s (halfWidth X (101/1000)) ≤
          C_R*halfWidth X (101/1000)/(Real.log X)^2) →
      Erdos374.MainStatement ∧
      Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
      ∃ c : ℝ, 0 < c ∧ ∃ cutoff : ℕ, ∀ N : ℕ, cutoff ≤ N →
        c*(N:ℝ) ≤ (Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  obtain ⟨s₀,hs₀,hs₁,hendpoint⟩ :=
    ShortSingletonClosure.eventually_erdos_conclusions_of_source_and_rest_negative_mean
  refine ⟨s₀,hs₀,hs₁,?_⟩
  intro s hs hss C_R hrest
  exact hendpoint s hs hss 1 C_R original_source_mean hrest

end Item1OriginalEndpointBridge

run_cmd do
  for target in [``Item1OriginalEndpointBridge.original_source_mean,
      ``Item1OriginalEndpointBridge.eventually_erdos_conclusions_of_rest_negative_mean] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "ORIGINAL ERDOS ENDPOINT BRIDGE: 2 standard-axiom theorem guards passed."

#check Item1OriginalEndpointBridge.eventually_erdos_conclusions_of_rest_negative_mean
#print axioms Item1OriginalEndpointBridge.eventually_erdos_conclusions_of_rest_negative_mean
