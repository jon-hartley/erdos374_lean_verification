import RosserKernelIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Direct integral estimate for the first-prime form of the ideal accepted
two-step operator. This avoids assuming an unproved interchange of integrals. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Set MeasureTheory
namespace RosserInnerIntegral

def inner (s : ℝ) : ℝ := exp (-max 2 (s-1))/s

theorem inner_nonneg (s : ℝ) (hs : 1 ≤ s) : 0 ≤ inner s := by
  exact div_nonneg (exp_pos _).le (by linarith)

theorem inner_le_exp (s : ℝ) (hs : 1 ≤ s) : inner s ≤ exp 1 * exp (-s) := by
  have he : exp (-max 2 (s-1)) ≤ exp (1-s) := by
    apply Real.exp_le_exp.mpr
    have h := le_max_right (2 : ℝ) (s-1)
    linarith
  unfold inner
  calc
    _ ≤ exp (1-s)/s := div_le_div_of_nonneg_right he (by linarith)
    _ ≤ exp (1-s) := (div_le_iff₀ (by linarith : 0 < s)).mpr
      (by nlinarith [exp_pos (1-s)])
    _ = _ := by rw [← Real.exp_add]; congr 1

theorem inner_integrable (a : ℝ) (ha : 1 ≤ a) : IntegrableOn inner (Ioi a) := by
  have hc : ContinuousOn inner (Ioi a) := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    unfold inner
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    linarith [hs.out]
  apply ((integrableOn_exp_neg_Ioi a).const_mul (exp 1)).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (inner_nonneg s (ha.trans hs.le))]
  exact inner_le_exp s (ha.trans hs.le)

theorem inner_tail_bound (a : ℝ) (ha : 3 ≤ a) :
    (∫ s in Ioi a, inner s) ≤ exp (1-a)/a := by
  have hbound : ∀ s ∈ Ioi a, inner s ≤ (exp 1/a)*exp (-s) := by
    intro s hs
    unfold inner
    rw [max_eq_right (by linarith [hs.out])]
    calc
      _ = exp 1 * exp (-s)/s := by rw [← Real.exp_add]; congr 2; ring
      _ ≤ exp 1 * exp (-s)/a := div_le_div_of_nonneg_left (by positivity)
        (by linarith) hs.le
      _ = _ := by ring
  have h := setIntegral_mono_on (inner_integrable a (by linarith))
    ((integrableOn_exp_neg_Ioi a).const_mul (exp 1/a)) measurableSet_Ioi hbound
  rw [integral_const_mul, integral_exp_neg_Ioi] at h
  convert h using 1
  rw [show exp 1/a * exp (-a) = (exp 1 * exp (-a))/a by ring, ← Real.exp_add]
  rfl

theorem inner_low_integral (a : ℝ) (ha : 1 ≤ a) (ha3 : a ≤ 3) :
    (∫ s in a..3, inner s) = exp (-2)*log (3/a) := by
  calc
    _ = ∫ s in a..3, exp (-2)*(1/s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ha3] at hs
      unfold inner
      rw [max_eq_left (by linarith [hs.2])]
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul,
      integral_one_div_of_pos (by linarith) (by norm_num)]

theorem weighted_inner_le_majorant (r : ℝ) (hr : 2 ≤ r) :
    exp r/r * (∫ s in Ioi (r-1), inner s) ≤ RosserKernelContraction.majorant r := by
  have hrp : 0 < r := by linarith
  unfold RosserKernelContraction.majorant
  split_ifs with h4
  · have hs := intervalIntegral.integral_Ioi_sub_Ioi
      (inner_integrable (r-1) (by linarith)) (by linarith : r-1 ≤ 3)
    rw [inner_low_integral (r-1) (by linarith) (by linarith)] at hs
    have ht := inner_tail_bound 3 (by norm_num)
    norm_num at ht
    have hh : (∫ s in Ioi (r-1), inner s) ≤
        exp (-2)*(log (3/(r-1))+1/3) := by linarith
    apply (mul_le_mul_of_nonneg_left hh (div_nonneg (exp_pos r).le hrp.le)).trans_eq
    rw [show exp r/r * (exp (-2)*(log (3/(r-1))+1/3)) =
      (exp r * exp (-2))/r * (log (3/(r-1))+1/3) by ring, ← Real.exp_add]
    congr 2
  · have h := inner_tail_bound (r-1) (by linarith)
    apply (mul_le_mul_of_nonneg_left h (div_nonneg (exp_pos r).le hrp.le)).trans_eq
    rw [show exp r/r * (exp (1-(r-1))/(r-1)) =
      (exp r * exp (1-(r-1)))/(r*(r-1)) by field_simp,
      ← Real.exp_add, show r+(1-(r-1)) = 2 by ring]

theorem inner_contraction (r : ℝ) (hr : 2 ≤ r) :
    (1/r)*(∫ s in Ioi (r-1), inner s) ≤ (99/100)*exp (-r) := by
  have h := (weighted_inner_le_majorant r hr).trans
    (RosserKernelContraction.majorant_le r hr)
  have he : exp (-r)*exp r = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hh := mul_le_mul_of_nonneg_left h (exp_pos (-r)).le
  calc
    _ = exp (-r)*(exp r/r*(∫ s in Ioi (r-1), inner s)) := by
      rw [show exp (-r)*(exp r/r*(∫ s in Ioi (r-1), inner s)) =
        (exp (-r)*exp r)/r*(∫ s in Ioi (r-1), inner s) by ring, he]
    _ ≤ exp (-r)*(99/100) := hh
    _ = _ := by ring

run_cmd do
  for decl in [``inner_nonneg, ``inner_le_exp, ``inner_integrable, ``inner_tail_bound,
    ``inner_low_integral, ``weighted_inner_le_majorant, ``inner_contraction] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end RosserInnerIntegral
end
