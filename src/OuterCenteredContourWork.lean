import OuterTruncatedContinuousWork

/-! The full literal localized remainder differs negligibly from the
assembled truncated discrete-minus-continuous contour. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterCenteredContourWork
open OuterSharpContourAssemblyWork OuterSharpContourWork OuterBlockContourTailWork
open OuterTruncatedContinuousWork OuterBlockMainTermWork OuterBlockSharpCompletionWork
open OuterMainCorrectionWork OuterActiveDyadicWork OuterSourceCubeIntegralWork
open OuterPairSourceDecompositionWork OuterLocalizedCoreWork

def tailError (X s x δ : ℝ) : ℂ := aggregate X s (fun i j k ω =>
  continuousContour X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k ω-
    truncatedContinuous X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k ω)

def centeredRemainder (X s x δ : ℝ) : ℝ := (aggregate X s (fun i j k ω =>
  discreteContour X s x δ i j k ω-
    truncatedContinuous X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k ω)).re

theorem centered_identity (X s x δ : ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2)) (hε : X^(-19/20:ℝ)∈Ioo 0 (1/4)) :
    centeredRemainder X s x δ-contourRemainder X s x δ=(tailError X s x δ).re := by
  have hσ : 1<1+1/Real.log X := by
    have : 0<1/Real.log X := by positivity
    linarith
  have hσ2 : 1+1/Real.log X≤2 := by
    have := (div_le_one (by linarith : 0<Real.log X)).mpr (show 1≤Real.log X by linarith)
    linarith
  simp only [centeredRemainder,contourRemainder,tailError,aggregate,Complex.re_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  apply Finset.sum_congr rfl
  intro k hk
  have hscale := (OuterBlockCofactorScaleWork.active_lower X s hX2 hs hlog ij.1 ij.2 k hk).1
  have hif := density_full_integrable X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) (X^4)
    ij.1 ij.2 k hX2 hx hδ hε hσ hσ2 hscale
  have hit := density_truncated_integrable X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) (X^4)
    ij.1 ij.2 k hX2 hx hδ ⟨hε.1,by linarith [hε.2]⟩ hσ hσ2 hscale
  have hid := OuterSharpContourRegularityWork.density_discrete_integrable X s x δ (X^4)
    ij.1 ij.2 k hX hX2 hx hδ
  simp_rw [mul_sub]
  rw [integral_sub hid hit,integral_sub hid hif,integral_sub hif hit]
  simp only [Complex.sub_re]
  ring

theorem eventually_tail_error (s : ℝ) (hs : 0≤s) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 2≤X ∧ ∀x δ : ℝ, x∈Icc X (2*X) → δ∈Icc 0 (1/2) →
      ‖tailError X s x δ‖≤X^(1/10:ℝ)/(Real.log X)^A := by
  have hεlim : Tendsto (fun X : ℝ => X^(-19/20:ℝ)) atTop (nhds 0) := by
    simpa only [neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<19/20))
  filter_upwards [eventually_ge_atTop (Real.exp 1),eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ)),
    hεlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    PolynomialLogEnvelope.eventually_bound (256*Real.exp 1*totalConstant s) (13+A) (1/10)
      (by have := totalConstant_nonneg s; positivity) (by norm_num)]
    with X hX hX2 hlog hε hbudget
  refine ⟨hX2,?_⟩
  intro x δ hx hδ
  have hXp : 0<X := by linarith
  have hl : 0<Real.log X := by linarith
  have hb := aggregate_bound X s (256*Real.exp 1) hX2 (by positivity)
    (fun i j k ω => continuousContour X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k ω-
      truncatedContinuous X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k ω)
    (fun i j k hk ω => truncation_bound X s x δ (X^(-19/20:ℝ)) i j k ω hX hX2 hx hδ
      ⟨by positivity,hε⟩ (OuterBlockCofactorScaleWork.active_lower X s hX2 hs hlog i j k hk).1)
  apply hb.trans
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  apply le_trans _ hbudget.2
  rw [pow_add,←mul_assoc]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le (by linarith) A)
    (by have := totalConstant_nonneg s; positivity)

theorem eventually_localized_centered (s : ℝ) (hs : 0≤s) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 256≤X ∧ ∀x Y : ℝ, x∈Icc X (2*X) →
      X^(1/10:ℝ)≤Y → Y≤X/2 →
      |localizedRemainder X s (x-x*(Y/X)) x-centeredRemainder X s x (Y/X)|≤3*Y/(Real.log X)^A := by
  have hεlim : Tendsto (fun X : ℝ => X^(-19/20:ℝ)) atTop (nhds 0) := by
    simpa only [neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<19/20))
  filter_upwards [eventually_tail_error s hs A,eventually_localized_contour s hs A,
    eventually_ge_atTop (Real.exp 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ)),
    hεlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))] with X htail hcont hX hlog hε
  refine ⟨hcont.1,?_⟩
  intro x Y hx hY hYX
  have hXp : 0<X := by linarith [hcont.1]
  have hY0 : 0≤Y := (Real.rpow_nonneg hXp.le _).trans hY
  have hδ : Y/X∈Icc (0:ℝ) (1/2) := ⟨div_nonneg hY0 hXp.le,(div_le_iff₀ hXp).mpr (by linarith)⟩
  have he := centered_identity X s x (Y/X) hX htail.1 hs hlog hx hδ ⟨by positivity,hε⟩
  have hb : |contourRemainder X s x (Y/X)-centeredRemainder X s x (Y/X)|≤Y/(Real.log X)^A := by
    rw [abs_sub_comm,he]
    exact (Complex.abs_re_le_norm _).trans ((htail.2 x (Y/X) hx hδ).trans
      (div_le_div_of_nonneg_right hY (by positivity)))
  exact ((abs_sub_le _ (contourRemainder X s x (Y/X)) _).trans
    (add_le_add (hcont.2 x Y hx hY hYX) hb)).trans_eq (by ring)

run_cmd do
  for decl in [``centered_identity, ``eventually_tail_error, ``eventually_localized_centered] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterCenteredContourWork
