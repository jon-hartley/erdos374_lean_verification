import SmoothedWindowTransfer

/-!
Continuity and integrability of the spatial smoothed window transform
on positive compact intervals. The proof uses the existing Fourier
factorization, avoiding assumptions about an undefined integral.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set

namespace SmoothedWindowRegularity
open SmoothedWindowTransfer SmoothMellinMultiplier MellinWindowFactor

theorem continuousOn_transform (F : ℝ → ℂ) (Ψ : ℝ → ℝ) (ε a b σ δ : ℝ)
    (hF : Continuous F) (hε : ε ∈ Ioo 0 1) (hσ : 0 < σ) (hδ : δ < 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, Ψ x / x = 1) :
    ContinuousOn (transform F Ψ ε a b σ δ) (Ioi 0) := by
  let g := fun t => (F t * multiplier Ψ ε σ t) * factor σ δ t
  have hg : Continuous g :=
    (hF.mul (continuous_multiplier Ψ ε σ hε hσ hdiff hnonneg hsupport hmass)).mul
      (continuous_factor σ δ hσ hδ)
  let G := CompactIntegral.transform FourierIntegralMeanSquare.kernel g a b
  have hG : Continuous G := CompactIntegral.continuous_transform
    FourierIntegralMeanSquare.kernel g a b FourierIntegralMeanSquare.continuous_kernel hg
  have hpow : ContinuousOn (fun x : ℝ => ((x ^ σ : ℝ) : ℂ)) (Ioi 0) := by
    exact Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx)))
  have hlog : ContinuousOn Real.log (Ioi 0) := by
    intro x hx
    exact (Real.continuousAt_log (ne_of_gt hx)).continuousWithinAt
  apply (hpow.mul (hG.comp_continuousOn hlog)).congr
  intro x hx
  rw [SmoothedWindowTransfer.transform_eq F Ψ ε a b σ δ x hσ,
    MellinWindowTransfer.transform_eq _ a b σ δ x hx hδ,
    MellinIntegralMeanSquare.transform_factor g a b σ x hx]
  rfl

theorem integrableOn_norm_sq (F : ℝ → ℂ) (Ψ : ℝ → ℝ) (ε a b σ δ X Z : ℝ)
    (hF : Continuous F) (hε : ε ∈ Ioo 0 1) (hσ : 0 < σ) (hδ : δ < 1)
    (hX : 0 < X) (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, Ψ x / x = 1) :
    IntegrableOn (fun x => ‖transform F Ψ ε a b σ δ x‖ ^ 2) (Icc X Z) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact ((continuousOn_transform F Ψ ε a b σ δ hF hε hσ hδ
    hdiff hnonneg hsupport hmass).norm.pow 2).mono (fun x hx => hX.trans_le hx.1)

end SmoothedWindowRegularity

#print axioms SmoothedWindowRegularity.integrableOn_norm_sq
run_cmd do
  let axioms ← Lean.collectAxioms ``SmoothedWindowRegularity.integrableOn_norm_sq
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "SMOOTHED WINDOW REGULARITY PASSED"
