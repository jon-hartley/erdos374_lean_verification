import OuterRampConvolutionWork
import OuterKernelIntegrableWork
import Mathlib.Analysis.Fourier.Inversion

/-! Exact Fourier transform and inversion of the compactified source
ramp. Mathlib's Fourier variable has the 2*pi normalization. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set FourierTransform
open scoped FourierTransform Convolution
namespace OuterRampFourierWork
open OuterRampConvolutionWork OuterRampAverageWork OuterSmoothStepWork
open OuterBoxFourierKernelWork OuterKernelIntegrableWork OuterMaskFrequencyWork

theorem fourier_intervalBox (a b ξ : ℝ) (hab : a ≤ b) :
    𝓕 (intervalBox a b) ξ = boxKernel a b (2*Real.pi*ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun v : ℝ => Complex.exp (↑(-2*Real.pi*v*ξ)*Complex.I) • intervalBox a b v) =
      (Ico a b).indicator (fun v : ℝ => Complex.exp (↑(-2*Real.pi*v*ξ)*Complex.I)) := by
    ext v
    by_cases hv : v ∈ Ico a b <;> simp [intervalBox,hv]
  rw [he,integral_indicator measurableSet_Ico,integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_congr
  intro v _
  unfold phase
  congr 1
  push_cast
  ring

theorem fourier_uniformBox (δ ξ : ℝ) (hδ : 0 < δ) :
    𝓕 (uniformBox δ) ξ = boxKernel (-δ) δ (2*Real.pi*ξ)/(2*δ:ℝ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun v : ℝ => Complex.exp (↑(-2*Real.pi*v*ξ)*Complex.I) • uniformBox δ v) =
      (Ioc (-δ) δ).indicator (fun v : ℝ =>
        Complex.exp (↑(-2*Real.pi*v*ξ)*Complex.I) / (2*δ:ℝ)) := by
    ext v
    by_cases hv : v ∈ Ioc (-δ) δ <;> simp [uniformBox,hv,div_eq_mul_inv]
  rw [he,integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),intervalIntegral.integral_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro v _
  unfold phase
  congr 1
  push_cast
  ring

theorem fourier_ramp (δ M ξ : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) :
    𝓕 (ramp δ M) ξ = smoothedKernel 0 M δ (2*Real.pi*ξ) := by
  rw [← ramp_convolution δ M hδ hM,
    Real.fourier_mul_convolution_eq (uniformBox_integrable δ) (intervalBox_integrable 0 M),
    fourier_uniformBox δ ξ hδ,fourier_intervalBox 0 M ξ hM,smoothedKernel]
  ring

theorem ramp_continuous (δ M : ℝ) : Continuous (ramp δ M) := by
  exact Complex.continuous_ofReal.comp ((transition_continuous δ).sub
    ((transition_continuous δ).comp (continuous_id.sub continuous_const)))

theorem ramp_integrable (δ M : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) :
    Integrable (ramp δ M) := by
  rw [← ramp_convolution δ M hδ hM]
  exact (uniformBox_integrable δ).integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ)
    (intervalBox_integrable 0 M)

theorem ramp_fourier_integrable (δ M : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) :
    Integrable (𝓕 (ramp δ M)) := by
  have hh := (kernel_integrable 0 M δ hδ).comp_mul_left' (by positivity : 2*Real.pi ≠ 0)
  exact hh.congr (Filter.Eventually.of_forall (fun ξ => (fourier_ramp δ M ξ hδ hM).symm))

theorem ramp_inversion (δ M : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) :
    𝓕⁻ (fun ξ => smoothedKernel 0 M δ (2*Real.pi*ξ)) = ramp δ M := by
  have he : (fun ξ => smoothedKernel 0 M δ (2*Real.pi*ξ)) = 𝓕 (ramp δ M) := by
    ext ξ
    exact (fourier_ramp δ M ξ hδ hM).symm
  rw [he]
  exact (ramp_continuous δ M).fourierInv_fourier_eq
    (ramp_integrable δ M hδ hM) (ramp_fourier_integrable δ M hδ hM)

run_cmd do
  for decl in [``fourier_intervalBox, ``fourier_uniformBox, ``fourier_ramp,
      ``ramp_continuous, ``ramp_integrable, ``ramp_fourier_integrable, ``ramp_inversion] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterRampFourierWork
