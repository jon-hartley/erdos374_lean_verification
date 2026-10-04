import SourceLiteralMoments
import SourceFirstFactorSaving

/-! v6: actual retained source cells -> a middle-frequency energy estimate.
UNCOMPILED DRAFT. The ONLY analytic premise not constructed here is the
explicit pointwise bound on the FIRST literal source polynomial. Neither
moment estimates nor a physical source residual estimate are hypotheses.
This does NOT formalize the external prime-polynomial theorem or the
low/high-frequency centered transfer. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SourceLiteralMiddle
open PositiveInteriorModel PositiveInteriorCells SourceLiteralMoments SourceMassDischarge

def height (X : ℝ) : ℝ := X^(562/625:ℝ)

def middle (X T0 : ℝ) : Set ℝ := Icc (-height X) (height X) ∩ {t | T0 ≤ |t|}

def sourceProduct (X : ℝ) (j : ℕ × ℕ) (t : ℝ) : ℂ :=
  factor X j 0 t*factor X j 1 t*factor X j 2 t

theorem middle_measurable (X T0 : ℝ) : MeasurableSet (middle X T0) :=
  measurableSet_Icc.inter (isClosed_le continuous_const continuous_abs).measurableSet

theorem middle_subset (X T0 : ℝ) : middle X T0 ⊆ Icc (-height X) (height X) :=
  fun _ ht => ht.1

/-- Closed form for a useful log cap. It is strictly positive and at most one. -/
theorem cap_bounds (L : ℝ) (hL : 1 ≤ L) :
    0 < L^(-26000:ℝ) ∧ L^(-26000:ℝ) ≤ 1 := by
  have hLp : 0 < L := by linarith
  refine ⟨Real.rpow_pos_of_pos hLp _,?_⟩
  simpa only [Real.rpow_zero] using
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (-26000:ℝ) ≤ 0)

/-- Main new source bridge, with the exact exceptional range left explicit.
This is conditional on a pointwise prime cap, not a claim that the external
prime cap has been proved in Lean. -/
theorem middle_energy_of_first_factor_cap (X T0 : ℝ) (j : ℕ × ℕ)
    (hX : 2 ≤ X) (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X))
    (hsmall : ∀ t ∈ middle X T0,
      ‖factor X j 0 t‖ ≤ (1+Real.log X)^(-26000:ℝ)) :
    (∫ t in middle X T0, ‖sourceProduct X j t‖^2) ≤
      3*commonConstant/(1+Real.log X)^34 := by
  obtain ⟨β,hβ,hS,hm⟩ := actual_cell_moments X j hX hlog hj
  let L := 1+Real.log X
  let μ : Measure ℝ := volume.restrict (middle X T0)
  let a : Fin 3 → ℝ → ℝ := fun i t => ‖factor X j i t‖
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg (show 1 ≤ X by linarith)]
  have hLp : 0 < L := by linarith
  have hsub := middle_subset X T0
  have hc (i : Fin 3) : Continuous (fun t => a i t^(β i)) :=
    (factor_continuous X j i).norm.rpow_const (fun _ => Or.inr (by linarith [hβ i]))
  have hi (i : Fin 3) : Integrable (fun t => a i t^(β i)) μ :=
    (hc i).integrableOn_Icc.mono_set hsub
  have hb (i : Fin 3) : (∫ t, a i t^(β i) ∂μ) ≤ commonConstant*L^18 := by
    have hh := setIntegral_mono_set (μ := volume) (hc i).integrableOn_Icc
      (Filter.Eventually.of_forall (fun t => Real.rpow_nonneg (norm_nonneg _) _))
      (Filter.Eventually.of_forall hsub)
    exact hh.trans (hm i)
  have hmeas : AEStronglyMeasurable (fun t => (a 0 t*a 1 t*a 2 t)^2) μ :=
    ((((factor_continuous X j 0).norm.mul (factor_continuous X j 1).norm).mul
      (factor_continuous X j 2).norm).pow 2).aestronglyMeasurable
  have hsmallAE : ∀ᵐ t ∂μ, a 0 t ≤ L^(-26000:ℝ) := by
    filter_upwards [ae_restrict_mem (middle_measurable X T0)] with t ht
    exact hsmall t ht
  have hcall := SourceFirstFactorSaving.integral_of_cap μ (a 0) (a 1) (a 2)
    (β 0) (β 1) (β 2) (L^(-26000:ℝ)) (commonConstant*L^18)
    (fun t => norm_nonneg _) (fun t => norm_nonneg _) (fun t => norm_nonneg _)
    (hβ 0) (hβ 1) (hβ 2) hS (cap_bounds L hL).1 (cap_bounds L hL).2
    hsmallAE (hi 0) (hi 1) (hi 2) hmeas (hb 0) (hb 1) (hb 2)
  rw [SourceFirstFactorSaving.log_budget L commonConstant hLp] at hcall
  simpa only [sourceProduct,norm_mul,a,μ,L] using hcall

#check middle_energy_of_first_factor_cap
#print axioms middle_energy_of_first_factor_cap
run_cmd do
  for n in [``middle_measurable,``middle_subset,``cap_bounds,
      ``middle_energy_of_first_factor_cap] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "LITERAL SOURCE MIDDLE ENERGY: FIRST-FACTOR PRIME CAP REMAINS EXPLICIT"
end SourceLiteralMiddle
