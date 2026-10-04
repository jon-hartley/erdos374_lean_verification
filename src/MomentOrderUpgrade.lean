import CompactIntegral

/-!
A pointwise cap upgrades a real moment on one compact interval. The
increment may be zero and the function may vanish.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set

namespace MomentOrderUpgrade

theorem integral_bound (a b X k p ξ : ℝ) (F : ℝ → ℂ)
    (hX : 0 < X) (_hk : 0 ≤ k) (hp : 0 < p) (hξ : 0 ≤ ξ)
    (hF : ContinuousOn F (Icc a b))
    (hcap : ∀ t ∈ Icc a b, ‖F t‖ ≤ X ^ (-k)) :
    (∫ t in Icc a b, ‖F t‖ ^ (p + ξ)) ≤
      X ^ (-k * ξ) * (∫ t in Icc a b, ‖F t‖ ^ p) := by
  have hsmall : ContinuousOn (fun t => ‖F t‖ ^ p) (Icc a b) :=
    hF.norm.rpow_const (fun _ _ => Or.inr hp.le)
  have hlarge : ContinuousOn (fun t => ‖F t‖ ^ (p + ξ)) (Icc a b) :=
    hF.norm.rpow_const (fun _ _ => Or.inr (by linarith))
  rw [← integral_const_mul]
  apply integral_mono_ae hlarge.integrableOn_Icc
    (hsmall.integrableOn_Icc.const_mul (X ^ (-k * ξ)))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hcapξ : ‖F t‖ ^ ξ ≤ (X ^ (-k)) ^ ξ :=
    Real.rpow_le_rpow (norm_nonneg _) (hcap t ht) hξ
  calc
    _ = ‖F t‖ ^ p * ‖F t‖ ^ ξ := by
      rw [← Real.rpow_add_of_nonneg (norm_nonneg _) hp.le hξ]
    _ ≤ ‖F t‖ ^ p * (X ^ (-k)) ^ ξ :=
      mul_le_mul_of_nonneg_left hcapξ
        (Real.rpow_nonneg (norm_nonneg _) _)
    _ = X ^ (-k * ξ) * ‖F t‖ ^ p := by
      rw [← Real.rpow_mul hX.le]
      ring

theorem bound_of_moment (a b X k p ξ γ : ℝ) (F : ℝ → ℂ)
    (hX : 0 < X) (hk : 0 ≤ k) (hp : 0 < p) (hξ : 0 ≤ ξ)
    (hF : ContinuousOn F (Icc a b))
    (hcap : ∀ t ∈ Icc a b, ‖F t‖ ≤ X ^ (-k))
    (hmoment : (∫ t in Icc a b, ‖F t‖ ^ p) ≤ X ^ γ) :
    (∫ t in Icc a b, ‖F t‖ ^ (p + ξ)) ≤
      X ^ (γ - k * ξ) := by
  calc
    _ ≤ X ^ (-k * ξ) * (∫ t in Icc a b, ‖F t‖ ^ p) :=
      integral_bound a b X k p ξ F hX hk hp hξ hF hcap
    _ ≤ X ^ (-k * ξ) * X ^ γ :=
      mul_le_mul_of_nonneg_left hmoment (Real.rpow_nonneg hX.le _)
    _ = _ := by
      rw [← Real.rpow_add hX]
      congr 1
      ring

end MomentOrderUpgrade

#print axioms MomentOrderUpgrade.integral_bound
#print axioms MomentOrderUpgrade.bound_of_moment
run_cmd do
  for target in [``MomentOrderUpgrade.integral_bound,
      ``MomentOrderUpgrade.bound_of_moment] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "MOMENT ORDER UPGRADE PASSED"
