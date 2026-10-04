import CompactIntegral

/-!
Hölder for two complex factors on one compact real interval, with
arbitrary real moment orders above two. The exponent identity is explicit
so callers cannot silently use moments on different scales.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set

namespace RealProductHolder

theorem bound (a b p q : ℝ) (F G : ℝ → ℂ)
    (hp : 2 < p) (hq : 2 < q) (hexponents : 2 / p + 2 / q = 1)
    (hF : ContinuousOn F (Icc a b))
    (hG : ContinuousOn G (Icc a b)) :
    (∫ x in Icc a b, ‖F x * G x‖ ^ 2) ≤
      (∫ x in Icc a b, ‖F x‖ ^ p) ^ (2 / p) *
        (∫ x in Icc a b, ‖G x‖ ^ q) ^ (2 / q) := by
  have hp_half : 1 < p / 2 := by linarith
  have hq_half : 1 < q / 2 := by linarith
  have hrecip : (p / 2)⁻¹ + (q / 2)⁻¹ = 1 := by
    have hp_ne : p ≠ 0 := by linarith
    have hq_ne : q ≠ 0 := by linarith
    field_simp [hp_ne, hq_ne] at hexponents ⊢
    linarith
  have hholder : (p / 2).HolderConjugate (q / 2) :=
    Real.holderConjugate_iff.mpr ⟨hp_half, hrecip⟩
  have hf : ContinuousOn (fun x => ‖F x‖ ^ 2) (Icc a b) := hF.norm.pow 2
  have hg : ContinuousOn (fun x => ‖G x‖ ^ 2) (Icc a b) := hG.norm.pow 2
  have hfi : MemLp (fun x => ‖F x‖ ^ 2) (ENNReal.ofReal (p / 2))
      (volume.restrict (Icc a b)) := by
    apply (integrable_norm_rpow_iff (hf.aestronglyMeasurable measurableSet_Icc)
      (ENNReal.ofReal_ne_zero_iff.mpr (by linarith)) (by simp)).mp
    have hc : ContinuousOn (fun x => ‖‖F x‖ ^ 2‖ ^ (p / 2))
        (Icc a b) :=
      hf.norm.rpow_const (fun _ _ => Or.inr (by linarith))
    rw [ENNReal.toReal_ofReal (by linarith)]
    exact hc.integrableOn_Icc
  have hgi : MemLp (fun x => ‖G x‖ ^ 2) (ENNReal.ofReal (q / 2))
      (volume.restrict (Icc a b)) := by
    apply (integrable_norm_rpow_iff (hg.aestronglyMeasurable measurableSet_Icc)
      (ENNReal.ofReal_ne_zero_iff.mpr (by linarith)) (by simp)).mp
    have hc : ContinuousOn (fun x => ‖‖G x‖ ^ 2‖ ^ (q / 2))
        (Icc a b) :=
      hg.norm.rpow_const (fun _ _ => Or.inr (by linarith))
    rw [ENNReal.toReal_ofReal (by linarith)]
    exact hc.integrableOn_Icc
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hholder
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖F x‖))
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖G x‖)) hfi hgi
  have hFpow (x : ℝ) : (‖F x‖ ^ 2) ^ (p / 2) = ‖F x‖ ^ p := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _)]
    congr 1
    ring
  have hGpow (x : ℝ) : (‖G x‖ ^ 2) ^ (q / 2) = ‖G x‖ ^ q := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _)]
    congr 1
    ring
  have hp_inv : 1 / (p / 2) = 2 / p := by
    field_simp [ne_of_gt (by linarith : 0 < p)]
  have hq_inv : 1 / (q / 2) = 2 / q := by
    field_simp [ne_of_gt (by linarith : 0 < q)]
  simp_rw [hFpow, hGpow] at hh
  rw [hp_inv, hq_inv] at hh
  simpa only [norm_mul, mul_pow] using hh

theorem bound_of_moments (a b p q X u v : ℝ) (F G : ℝ → ℂ)
    (hp : 2 < p) (hq : 2 < q) (hexponents : 2 / p + 2 / q = 1)
    (hX : 0 < X) (hF : ContinuousOn F (Icc a b))
    (hG : ContinuousOn G (Icc a b))
    (hFmoment : (∫ x in Icc a b, ‖F x‖ ^ p) ≤ X ^ u)
    (hGmoment : (∫ x in Icc a b, ‖G x‖ ^ q) ≤ X ^ v) :
    (∫ x in Icc a b, ‖F x * G x‖ ^ 2) ≤
      X ^ (u * (2 / p) + v * (2 / q)) := by
  have hFnonneg : 0 ≤ ∫ x in Icc a b, ‖F x‖ ^ p :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hGnonneg : 0 ≤ ∫ x in Icc a b, ‖G x‖ ^ q :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  calc
    _ ≤ (∫ x in Icc a b, ‖F x‖ ^ p) ^ (2 / p) *
          (∫ x in Icc a b, ‖G x‖ ^ q) ^ (2 / q) :=
      bound a b p q F G hp hq hexponents hF hG
    _ ≤ (X ^ u) ^ (2 / p) * (X ^ v) ^ (2 / q) := by
      gcongr
    _ = X ^ (u * (2 / p) + v * (2 / q)) := by
      rw [← Real.rpow_mul hX.le, ← Real.rpow_mul hX.le,
        ← Real.rpow_add hX]

end RealProductHolder

#print axioms RealProductHolder.bound
#print axioms RealProductHolder.bound_of_moments
run_cmd do
  for target in [``RealProductHolder.bound,
      ``RealProductHolder.bound_of_moments] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "REAL PRODUCT HOLDER PASSED"
