import Item1SharpCapScalarEnvelope
import Item1SharpDyadicSmoothing
import Item1SmoothedContourEstimate
import Item1SmoothCapScalar

/-!
The literal endpoint correction is added to the actual contour
estimate, then normalized with FIXED B. All scalar estimates have proof bodies.
PositiveStrip remains an explicit, unproved analytic premise in the sharp bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
namespace Item1SharpCapEnvelope
open Item1SharpDyadicSmoothing Item1ZetaContourGeometry
open Item1SmoothedContourEstimate Item1SmoothCapScalar

/-- The sharp half-open polynomial, not just its smoothed surrogate. -/
theorem sharp_envelope (N : ℕ) (hN : 1 ≤ N) (δ a C T₀ t : ℝ)
    (hlog : 2 ≤ Real.log (N:ℝ)) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (ha : 0 < a) (ha1 : a ≤ 1/2) (hC : 0 ≤ C) (hT : 4 ≤ T₀)
    (ht : 8 ≤ t) (htT : 2*T₀ ≤ t) (hs : PositiveStrip a C T₀) :
    ‖dyadic N t‖ ≤ envelope (Real.log (N:ℝ)) N δ a C (heightLog t) t := by
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := log_two_ge_half
  have hd := literal_desmoothing N hN δ t hlog hδ hδ1
  have hc := smoothed_bound_log_choice N δ a C T₀ t hNr hlog
    hδ (hδ1.trans hlog2) ha ha1 hC hT ht htT hs
  have hn := norm_add_le (dyadic N t-Item1RampDirichlet.smoothFinite N δ t)
    (Item1RampDirichlet.smoothFinite N δ t)
  rw [sub_add_cancel] at hn
  exact hn.trans (by unfold envelope; linarith)

end Item1SharpCapEnvelope

-- ROOT CAP RECURSIVE AUDIT: original declarations only.
run_cmd do
  for target in [
    ``Item1SharpCapEnvelope.sharp_envelope,
    ``Item1SharpCapEnvelope.smoothing_range,
    ``Item1SharpCapEnvelope.height_log_upper,
    ``Item1SharpCapEnvelope.depth_saving,
    ``Item1SharpCapEnvelope.monomial_normalizations,
    ``Item1SharpCapEnvelope.frequency_divisions,
    ``Item1SharpCapEnvelope.normalized_envelope] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1SharpCapEnvelope: 7 original theorem guards passed."
