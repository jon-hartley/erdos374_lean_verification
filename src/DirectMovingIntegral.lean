import PairSpacingKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Elementary integral Cauchy and compact-rectangle Fubini. The motion
bound retains both factors of the parameter interval length. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Set MeasureTheory

namespace Erdos374.DirectMovingIntegral

theorem real_integral_cauchy (f : ℝ → ℝ) (hf : Continuous f)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, f t)^2 ≤ (b-a)*(∫ t in a..b, (f t)^2) := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst b
    simp
  let I := ∫ t in a..b, f t
  have hL : 0 < b-a := sub_pos.mpr hlt
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab
    ((continuous_const.mul hf).intervalIntegrable a b)
    (((continuous_const.mul (hf.pow 2)).add continuous_const).intervalIntegrable a b)
    (fun t (_ht : t ∈ Icc a b) =>
      show 2*(b-a)*I*f t ≤ (b-a)^2*(f t)^2+I^2 from by
        nlinarith [sq_nonneg ((b-a)*f t-I)])
  change (∫ t in a..b, 2*(b-a)*I*f t) ≤
    ∫ t in a..b, (b-a)^2*(f t)^2+I^2 at hm
  have hi1 : IntervalIntegrable (fun t => (b-a)^2*(f t)^2) volume a b :=
    (continuous_const.mul (hf.pow 2)).intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun _ : ℝ => I^2) volume a b :=
    continuous_const.intervalIntegrable a b
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hm
  change 2*(b-a)*I*I ≤ (b-a)^2*(∫ t in a..b, (f t)^2)+(b-a)*I^2 at hm
  have hh : (b-a)*I^2 ≤ (b-a)*((b-a)*(∫ t in a..b, (f t)^2)) := by nlinarith [hm]
  exact le_of_mul_le_mul_left hh hL

theorem complex_integral_cauchy (f : ℝ → ℂ) (hf : Continuous f)
    (a b : ℝ) (hab : a ≤ b) :
    ‖∫ t in a..b, f t‖^2 ≤ (b-a)*(∫ t in a..b, ‖f t‖^2) := by
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := f) hab
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (real_integral_cauchy _ hf.norm a b hab)

theorem continuous_rectangle_swap (F : ℝ → ℝ → ℝ)
    (hF : Continuous F.uncurry) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in a..b, ∫ t in c..d, F x t) = ∫ t in c..d, ∫ x in a..b, F x t := by
  apply intervalIntegral_intervalIntegral_swap
  rw [uIoc_of_le hab, uIoc_of_le hcd]
  exact (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem low_motion_bound (P d : ℝ → ℂ) (hP : Continuous P) (hd : Continuous d)
    (X α M : ℝ) (hX : 0 < X) (hα : α ≤ 1)
    (he : ∀ x ∈ Icc X (2*X),
      P x-P (α*x) = (x:ℂ)*(∫ t in α..1, d (t*x)))
    (hM : ∀ t ∈ Icc α 1, (∫ x in X..2*X, ‖d (t*x)‖^2) ≤ M) :
    (∫ x in X..2*X, ‖P x-P (α*x)‖^2) ≤ 4*X^2*(1-α)^2*M := by
  have hX2 : X ≤ 2*X := by linarith
  have hlen : 0 ≤ 1-α := sub_nonneg.mpr hα
  have hjoint : Continuous (fun z : ℝ×ℝ => ‖d (z.2*z.1)‖^2) := by fun_prop
  have hpar : Continuous (fun x : ℝ => ∫ t in α..1, ‖d (t*x)‖^2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hjoint α 1
  have houter : Continuous (fun x => ‖P x-P (α*x)‖^2) := by fun_prop
  have hpoint (x : ℝ) (hx : x ∈ Icc X (2*X)) :
      ‖P x-P (α*x)‖^2 ≤ 4*X^2*(1-α)*(∫ t in α..1, ‖d (t*x)‖^2) := by
    have hx0 : 0 ≤ x := hX.le.trans hx.1
    have hx2 : x^2 ≤ 4*X^2 := by nlinarith [hx.2]
    have hc := complex_integral_cauchy (fun t => d (t*x)) (by fun_prop) α 1 hα
    have hi : 0 ≤ ∫ t in α..1, ‖d (t*x)‖^2 :=
      intervalIntegral.integral_nonneg_of_forall hα (fun _ => sq_nonneg _)
    calc
      _ = x^2*‖∫ t in α..1, d (t*x)‖^2 := by
        rw [he x hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0, mul_pow]
      _ ≤ x^2*((1-α)*(∫ t in α..1, ‖d (t*x)‖^2)) :=
        mul_le_mul_of_nonneg_left hc (sq_nonneg x)
      _ ≤ 4*X^2*((1-α)*(∫ t in α..1, ‖d (t*x)‖^2)) :=
        mul_le_mul_of_nonneg_right hx2 (mul_nonneg hlen hi)
      _ = _ := by ring
  have ho := intervalIntegral.integral_mono_on (μ := volume) hX2 (houter.intervalIntegrable X (2*X))
    ((continuous_const.mul hpar).intervalIntegrable X (2*X)) hpoint
  change (∫ x in X..2*X, ‖P x-P (α*x)‖^2) ≤
    ∫ x in X..2*X, 4*X^2*(1-α)*(∫ t in α..1, ‖d (t*x)‖^2) at ho
  rw [intervalIntegral.integral_const_mul,
    continuous_rectangle_swap (fun x t => ‖d (t*x)‖^2) hjoint X (2*X) α 1 hX2 hα] at ho
  have hreverse : Continuous (fun z : ℝ×ℝ => ‖d (z.1*z.2)‖^2) := by fun_prop
  have hslice : Continuous (fun t => ∫ x in X..2*X, ‖d (t*x)‖^2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hreverse X (2*X)
  have hm := intervalIntegral.integral_mono_on (μ := volume) hα (hslice.intervalIntegrable α 1)
    (continuous_const.intervalIntegrable α 1) hM
  rw [intervalIntegral.integral_const, smul_eq_mul] at hm
  calc
    _ ≤ 4*X^2*(1-α)*(∫ t in α..1, ∫ x in X..2*X, ‖d (t*x)‖^2) := ho
    _ ≤ 4*X^2*(1-α)*((1-α)*M) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

run_cmd do
  for target in [``real_integral_cauchy, ``complex_integral_cauchy,
      ``continuous_rectangle_swap, ``low_motion_bound] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "DirectMovingIntegral PASSED; 4 declarations guarded; both parameter-length factors retained"
end Erdos374.DirectMovingIntegral
end
