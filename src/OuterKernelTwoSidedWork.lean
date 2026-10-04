import OuterKernelIntegrableWork
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Whole-line logarithmic norm and infinite-tail estimates for the
averaging kernel, extending the finite positive-frequency bounds. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate
namespace OuterKernelTwoSidedWork
open OuterBoxFourierKernelWork OuterBoxFourierTailWork OuterKernelIntegrableWork
open OuterMaskFrequencyWork

theorem boxKernel_neg (a b t : ℝ) : boxKernel a b (-t) = conj (boxKernel a b t) := by
  unfold boxKernel
  have hc (f : ℝ → ℂ) : (∫x in a..b, conj (f x)) = conj (∫x in a..b, f x) := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,integral_conj,
      ← RCLike.conj_smul,← intervalIntegral.intervalIntegral_eq_integral_uIoc]
  rw [← hc]
  apply intervalIntegral.integral_congr
  intro x _
  simp [phase,← Complex.exp_conj]

theorem kernel_norm_even (a b δ t : ℝ) :
    ‖smoothedKernel a b δ (-t)‖ = ‖smoothedKernel a b δ t‖ := by
  simp only [smoothedKernel,boxKernel_neg,norm_div,norm_mul,Complex.norm_conj]

theorem kernel_positive_infinite (a b δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫t in Ioi (0:ℝ), ‖smoothedKernel a b δ t‖) ≤ |b-a|+2*Real.log (δ⁻¹)+2 := by
  apply le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0
    (kernel_integrable a b δ hδ).norm.integrableOn tendsto_id)
  filter_upwards [eventually_ge_atTop δ⁻¹] with U hU
  exact kernel_uniform_positive_integral a b δ U hδ hδ1 hU

theorem kernel_positive_tail (a b δ T : ℝ) (hδ : 0 < δ) (hT : 0 < T) :
    (∫t in Ioi T, ‖smoothedKernel a b δ t‖) ≤ 2/(δ*T) := by
  apply le_of_tendsto (intervalIntegral_tendsto_integral_Ioi T
    (kernel_integrable a b δ hδ).norm.integrableOn tendsto_id)
  filter_upwards [eventually_ge_atTop T] with U hU
  exact kernel_tail_integral a b δ T U hδ hT hU

theorem kernel_negative_tail (a b δ T : ℝ) (hδ : 0 < δ) (hT : 0 < T) :
    (∫t in Iic (-T), ‖smoothedKernel a b δ t‖) ≤ 2/(δ*T) := by
  rw [← integral_comp_neg_Ioi]
  simpa only [kernel_norm_even] using kernel_positive_tail a b δ T hδ hT

theorem kernel_whole_norm (a b δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫t, ‖smoothedKernel a b δ t‖) ≤ 2*|b-a|+4*Real.log (δ⁻¹)+4 := by
  have hp := kernel_positive_infinite a b δ hδ hδ1
  have he : (∫t in Iic (0:ℝ), ‖smoothedKernel a b δ t‖) =
      ∫t in Ioi (0:ℝ), ‖smoothedKernel a b δ t‖ := by
    simpa only [kernel_norm_even,neg_zero] using
      (integral_comp_neg_Iic 0 (fun t => ‖smoothedKernel a b δ t‖))
  have hs := integral_add_compl (s := Iic (0:ℝ)) measurableSet_Iic (kernel_integrable a b δ hδ).norm
  rw [compl_Iic] at hs
  rw [← hs,he]
  linarith

run_cmd do
  for decl in [``boxKernel_neg, ``kernel_norm_even, ``kernel_positive_infinite,
      ``kernel_positive_tail, ``kernel_negative_tail, ``kernel_whole_norm] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterKernelTwoSidedWork
