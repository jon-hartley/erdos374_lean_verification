import Item1PhaseZetaGrowth
import Item1GrowthToZeroFree

/-! The original phase-input contract and growth implication are factored out
of the final source-integral endpoint. The added corollary connects the same
unproved input directly to the eventual zero-free region. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set
namespace Item1IntermediatePhaseEndpoint
open Item1DyadicPhaseReduction Item1PhaseZetaGrowth Item1GrowthToZeroFree

/-- This remains the exact missing arithmetic contract. -/
def IntermediatePhaseInput (T : ℝ) : Prop :=
  ∀ t : ℝ, T≤t → IntermediateDyadicPhaseAt t

theorem left_growth_of_intermediate_phase (T : ℝ) (hcore : IntermediatePhaseInput T) :
    LeftLogarithmicZetaGrowth 7 128 (max T (Real.exp 8)) := by
  intro sigma t ht hstrip hs1
  have htp : 0<t := (Real.exp_pos 8).trans_le ((le_max_right T _).trans ht)
  have hL : 8≤Real.log t :=
    (Real.le_log_iff_exp_le htp).mpr ((le_max_right T _).trans ht)
  have ht2 : 2≤t := by
    have hh := Real.add_one_le_exp (8:ℝ)
    linarith [(le_max_right T (Real.exp 8)).trans ht]
  have hh := zeta_growth_from_intermediate_phase sigma t ht2 hL hstrip hs1
    (hcore t ((le_max_left T _).trans ht))
  simpa only [line] using hh

/-- Conditional on the same all-prefix estimate; the hypothesis is not discharged. -/
theorem eventually_zero_free_of_intermediate_phase (T : ℝ)
    (hcore : IntermediatePhaseInput T) :
    ∀ᶠ t : ℝ in atTop, ∀ beta : ℝ,
      1-(1/20)/(Real.log t)^(3/4:ℝ)≤beta →
      riemannZeta ((beta:ℂ)+(t:ℂ)*Complex.I)≠0 := by
  obtain ⟨A,C,Tg,hC,hg⟩ := extend_left_growth 7 128 (max T (Real.exp 8))
    (by norm_num) (left_growth_of_intermediate_phase T hcore)
  exact eventually_zero_free_of_growth A C Tg hC hg

/-- The same conclusion in the original downstream strip contract. -/
theorem bare_zero_free_of_intermediate_phase (T : ℝ) (hcore : IntermediatePhaseInput T) :
    ∃ T₀ : ℝ, 4≤T₀ ∧ Item1ZetaDiskGeometry.BarePositiveZeroFree (1/20) T₀ := by
  exact bare_zero_free_of_left_growth 7 128 (max T (Real.exp 8))
    (by norm_num) (left_growth_of_intermediate_phase T hcore)

end Item1IntermediatePhaseEndpoint

#check Item1IntermediatePhaseEndpoint.bare_zero_free_of_intermediate_phase
#print axioms Item1IntermediatePhaseEndpoint.bare_zero_free_of_intermediate_phase

run_cmd do
  for target in [``Item1IntermediatePhaseEndpoint.left_growth_of_intermediate_phase,
    ``Item1IntermediatePhaseEndpoint.eventually_zero_free_of_intermediate_phase,
    ``Item1IntermediatePhaseEndpoint.bare_zero_free_of_intermediate_phase] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
