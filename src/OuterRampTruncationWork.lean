import OuterSourceFourierWork
import OuterKernelTwoSidedWork

/-! Uniform angular-frequency truncation of the actual compact ramp.
The remaining application work is nine-factor error aggregation and the
centered moving-window moment estimate. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace OuterRampTruncationWork
open OuterBoxFourierKernelWork OuterBoxFourierTailWork OuterKernelIntegrableWork
open OuterKernelTwoSidedWork OuterMaskFrequencyWork OuterRampFourierWork
open OuterRampConvolutionWork OuterSourceFourierWork

def integrand (δ M x t : ℝ) : ℂ := phase t x*smoothedKernel 0 M δ t

theorem integrand_norm (δ M x t : ℝ) :
    ‖integrand δ M x t‖ = ‖smoothedKernel 0 M δ t‖ := by
  simp only [integrand,norm_mul,phase_norm,one_mul]

theorem integrand_integrable (δ M x : ℝ) (hδ : 0 < δ) :
    Integrable (integrand δ M x) := by
  apply (kernel_integrable 0 M δ hδ).norm.mono'
  · have hc : Continuous (integrand δ M x) := by
      apply Continuous.mul _ (kernel_continuous 0 M δ)
      unfold phase
      fun_prop
    exact hc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => (integrand_norm δ M x t).le)

theorem integrand_tail_error (δ M x T : ℝ) (hδ : 0 < δ) (hT : 0 < T) :
    ‖(∫t, integrand δ M x t)-(∫t in -T..T, integrand δ M x t)‖ ≤ 4/(δ*T) := by
  have hf := integrand_integrable δ M x hδ
  have hs := intervalIntegral.integral_Iic_add_Ioi (b := T) hf.integrableOn hf.integrableOn
  have hm := intervalIntegral.integral_Iic_sub_Iic (a := -T) (b := T)
    hf.integrableOn hf.integrableOn
  have he : (∫t, integrand δ M x t)-(∫t in -T..T, integrand δ M x t) =
      (∫t in Iic (-T), integrand δ M x t)+(∫t in Ioi T, integrand δ M x t) := by
    linear_combination -hs + hm
  rw [he]
  calc
    _ ≤ ‖∫t in Iic (-T), integrand δ M x t‖+‖∫t in Ioi T, integrand δ M x t‖ := norm_add_le _ _
    _ ≤ (∫t in Iic (-T), ‖integrand δ M x t‖)+(∫t in Ioi T, ‖integrand δ M x t‖) :=
      add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _)
    _ = (∫t in Iic (-T), ‖smoothedKernel 0 M δ t‖)+
        (∫t in Ioi T, ‖smoothedKernel 0 M δ t‖) := by simp only [integrand_norm]
    _ ≤ 2/(δ*T)+2/(δ*T) := add_le_add (kernel_negative_tail 0 M δ T hδ hT)
      (kernel_positive_tail 0 M δ T hδ hT)
    _ = _ := by ring

theorem angular_inversion (δ M x : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) :
    ((2*Real.pi)⁻¹:ℝ) • (∫t, integrand δ M x t) = ramp δ M x := by
  have hh := congrFun (ramp_inversion δ M hδ hM) x
  rw [inverse_eq_phase_integral] at hh
  have he := Measure.integral_comp_mul_left (integrand δ M x) (2*Real.pi)
  rw [abs_of_pos (inv_pos.mpr (by positivity : 0 < 2*Real.pi))] at he
  exact he.symm.trans hh

def truncatedRamp (δ M T x : ℝ) : ℂ :=
  ((2*Real.pi)⁻¹:ℝ) • (∫t in -T..T, integrand δ M x t)

theorem ramp_truncation_error (δ M T x : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hT : 0 < T) :
    ‖ramp δ M x-truncatedRamp δ M T x‖ ≤ (2*Real.pi)⁻¹*(4/(δ*T)) := by
  rw [← angular_inversion δ M x hδ hM,truncatedRamp,← smul_sub,norm_smul,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by positivity : 0 < 2*Real.pi))]
  exact mul_le_mul_of_nonneg_left (integrand_tail_error δ M x T hδ hT) (by positivity)

run_cmd do
  for decl in [``integrand_norm, ``integrand_integrable, ``integrand_tail_error,
      ``angular_inversion, ``ramp_truncation_error] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterRampTruncationWork
