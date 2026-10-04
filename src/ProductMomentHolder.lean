import CompactIntegral

/-!
Continuous product moment inequalities on a compact real interval.
Two Cauchy-Schwarz steps combine moments of orders eight, eight and four.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set

namespace ProductMomentHolder

theorem cauchy_square (a b : ℝ) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ x in Icc a b, f x * g x) ^ 2 ≤
      (∫ x in Icc a b, f x ^ 2) * (∫ x in Icc a b, g x ^ 2) := by
  have hfi : MemLp f 2 (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
      (hf.pow 2).continuousOn.integrableOn_Icc
  have hgi : MemLp g 2 (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr
      (hg.pow 2).continuousOn.integrableOn_Icc
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 from Real.holderConjugate_iff.mpr (by norm_num))
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (by simpa using hfi) (by simpa using hgi)
  norm_num only [Real.rpow_two] at hh
  have hfn : 0 ≤ ∫ x in Icc a b, f x ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hgn : 0 ≤ ∫ x in Icc a b, g x ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hn : 0 ≤ ∫ x in Icc a b, f x * g x :=
    integral_nonneg (fun x => mul_nonneg (hf0 x) (hg0 x))
  have hs := pow_le_pow_left₀ hn hh 2
  rw [mul_pow, ← Real.rpow_mul_natCast hfn, ← Real.rpow_mul_natCast hgn] at hs
  norm_num at hs
  exact hs

theorem eighth_eighth_fourth (a b : ℝ) (F G H : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G) (hH : Continuous H) :
    (∫ x in Icc a b, ‖F x * G x * H x‖ ^ 2) ^ 4 ≤
      (∫ x in Icc a b, ‖F x‖ ^ 8) *
        (∫ x in Icc a b, ‖G x‖ ^ 8) * (∫ x in Icc a b, ‖H x‖ ^ 4) ^ 2 := by
  have hfirst := cauchy_square a b
    (fun x => ‖F x‖ ^ 2 * ‖G x‖ ^ 2) (fun x => ‖H x‖ ^ 2)
    (by fun_prop) (by fun_prop) (by intro x; positivity) (by intro x; positivity)
  have hsecond := cauchy_square a b (fun x => ‖F x‖ ^ 4) (fun x => ‖G x‖ ^ 4)
    (by fun_prop) (by fun_prop) (by intro x; positivity) (by intro x; positivity)
  have hid (x : ℝ) : (‖F x‖ ^ 2 * ‖G x‖ ^ 2) ^ 2 = ‖F x‖ ^ 4 * ‖G x‖ ^ 4 := by ring
  have hfour (x : ℝ) : (‖H x‖ ^ 2) ^ 2 = ‖H x‖ ^ 4 := by ring
  simp_rw [hid, hfour] at hfirst
  have heighthF (x : ℝ) : (‖F x‖ ^ 4) ^ 2 = ‖F x‖ ^ 8 := by ring
  have heighthG (x : ℝ) : (‖G x‖ ^ 4) ^ 2 = ‖G x‖ ^ 8 := by ring
  simp_rw [heighthF, heighthG] at hsecond
  have hs := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  rw [mul_pow] at hs
  have ht := hs.trans (mul_le_mul_of_nonneg_right hsecond (sq_nonneg _))
  convert ht using 1
  simp_rw [norm_mul, mul_pow]
  ring

end ProductMomentHolder

#print axioms ProductMomentHolder.eighth_eighth_fourth
run_cmd do
  let axioms ← Lean.collectAxioms ``ProductMomentHolder.eighth_eighth_fourth
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "PRODUCT MOMENT HOLDER PASSED"
