import OuterBoxFourierKernelWork
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Explicit logarithmic integral and polynomial tail costs for the
interval-averaging Fourier kernel, on positive frequency intervals. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace OuterBoxFourierTailWork
open OuterMaskFrequencyWork OuterBoxFourierKernelWork

theorem boxKernel_continuousOn (a b T U : ℝ) (hT : 0 < T) :
    ContinuousOn (boxKernel a b) (Icc T U) := by
  have hc : ContinuousOn (fun t : ℝ =>
      (phase (-t) b-phase (-t) a)/(Complex.I*(-t:ℝ))) (Icc T U) := by
    apply ContinuousOn.div
    · unfold phase
      fun_prop
    · fun_prop
    · intro t ht
      exact mul_ne_zero Complex.I_ne_zero (by
        exact_mod_cast neg_ne_zero.mpr (ne_of_gt (hT.trans_le ht.1)))
  apply hc.congr
  intro t ht
  exact boxKernel_formula a b t (ne_of_gt (hT.trans_le ht.1))

theorem kernel_norm_integrable (a b δ T U : ℝ) (hT : 0 < T) (hTU : T ≤ U) :
    IntervalIntegrable (fun t => ‖smoothedKernel a b δ t‖) volume T U := by
  have hc : ContinuousOn (fun t => ‖smoothedKernel a b δ t‖) (Icc T U) := by
    exact ((boxKernel_continuousOn a b T U hT).mul
      (boxKernel_continuousOn (-δ) δ T U hT)).div_const _ |>.norm
  exact hc.intervalIntegrable_of_Icc hTU

theorem kernel_log_integral (a b δ T U : ℝ) (hδ : 0 < δ)
    (hT : 0 < T) (hTU : T ≤ U) :
    (∫t in T..U, ‖smoothedKernel a b δ t‖) ≤ 2*Real.log (U/T) := by
  have hg : IntervalIntegrable (fun t : ℝ => 2*t⁻¹) volume T U := by
    apply ContinuousOn.intervalIntegrable_of_Icc hTU
    exact continuousOn_const.mul (continuousOn_id.inv₀ (fun t ht =>
      ne_of_gt (hT.trans_le ht.1)))
  have hh := intervalIntegral.integral_mono_on hTU
    (kernel_norm_integrable a b δ T U hT hTU) hg (fun t ht => by
      simpa [abs_of_pos (hT.trans_le ht.1),div_eq_mul_inv] using
        smoothedKernel_first_decay a b δ t hδ (ne_of_gt (hT.trans_le ht.1)))
  simpa only [intervalIntegral.integral_const_mul,
    integral_inv_of_pos hT (hT.trans_le hTU)] using hh

theorem kernel_tail_integral (a b δ T U : ℝ) (hδ : 0 < δ)
    (hT : 0 < T) (hTU : T ≤ U) :
    (∫t in T..U, ‖smoothedKernel a b δ t‖) ≤ 2/(δ*T) := by
  have hg : IntervalIntegrable (fun t : ℝ => (2/δ)*(t^2)⁻¹) volume T U := by
    apply ContinuousOn.intervalIntegrable_of_Icc hTU
    exact continuousOn_const.mul ((continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero _ (ne_of_gt (hT.trans_le ht.1))))
  have hh := intervalIntegral.integral_mono_on hTU
    (kernel_norm_integrable a b δ T U hT hTU) hg (fun t ht => by
      convert smoothedKernel_second_decay a b δ t hδ
        (ne_of_gt (hT.trans_le ht.1)) using 1 <;> ring)
  have he : (∫t in T..U, (t^2)⁻¹) = T⁻¹-U⁻¹ := by
    have hz := integral_zpow (a := T) (b := U) (n := -2)
      (Or.inr ⟨by norm_num, notMem_uIcc_of_lt hT (hT.trans_le hTU)⟩)
    convert hz using 1 <;> simp <;> ring
  rw [intervalIntegral.integral_const_mul,he] at hh
  calc
    _ ≤ (2/δ)*(T⁻¹-U⁻¹) := hh
    _ ≤ (2/δ)*T⁻¹ := mul_le_mul_of_nonneg_left
      (sub_le_self _ (inv_nonneg.mpr (hT.trans_le hTU).le)) (by positivity)
    _ = _ := by ring

theorem kernel_continuous (a b δ : ℝ) : Continuous (smoothedKernel a b δ) := by
  have hc (a b : ℝ) : Continuous (boxKernel a b) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    unfold phase Function.uncurry
    fun_prop
  exact ((hc a b).mul (hc (-δ) δ)).div_const _

theorem kernel_low_integral (a b δ : ℝ) (hδ : 0 < δ) :
    (∫t in (0:ℝ)..1, ‖smoothedKernel a b δ t‖) ≤ |b-a| := by
  have hh := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (kernel_continuous a b δ |>.norm.intervalIntegrable 0 1)
    (intervalIntegrable_const (c := |b-a|))
    (fun t _ => smoothedKernel_length a b δ t hδ)
  simpa using hh

theorem kernel_positive_integral (a b δ T : ℝ) (hδ : 0 < δ) (hT : 1 ≤ T) :
    (∫t in (0:ℝ)..T, ‖smoothedKernel a b δ t‖) ≤ |b-a|+2*Real.log T := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (kernel_continuous a b δ |>.norm.intervalIntegrable 0 1)
    (kernel_continuous a b δ |>.norm.intervalIntegrable 1 T)]
  exact add_le_add (kernel_low_integral a b δ hδ)
    (by simpa using kernel_log_integral a b δ 1 T hδ (by norm_num) hT)

/-- The bound is uniform in the final cutoff U, after the smoothing scale. -/
theorem kernel_uniform_positive_integral (a b δ U : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hU : δ⁻¹ ≤ U) :
    (∫t in (0:ℝ)..U, ‖smoothedKernel a b δ t‖) ≤
      |b-a|+2*Real.log (δ⁻¹)+2 := by
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (kernel_continuous a b δ |>.norm.intervalIntegrable 0 δ⁻¹)
    (kernel_continuous a b δ |>.norm.intervalIntegrable δ⁻¹ U)]
  apply add_le_add (kernel_positive_integral a b δ δ⁻¹ hδ hδi)
  simpa [ne_of_gt hδ] using kernel_tail_integral a b δ δ⁻¹ U hδ (inv_pos.mpr hδ) hU

run_cmd do
  for decl in [``boxKernel_continuousOn, ``kernel_norm_integrable,
      ``kernel_log_integral, ``kernel_tail_integral, ``kernel_continuous,
      ``kernel_low_integral, ``kernel_positive_integral, ``kernel_uniform_positive_integral] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBoxFourierTailWork
