import OuterRampFourierWork
import OuterRampLengthWork

/-! Unconditional Fourier inversion for each of the nine continuous source
cuts on the actual enlarged ambient family. This is an exact product of
absolutely convergent one-dimensional integrals, before truncation or
moving-window moment assembly. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
namespace OuterSourceFourierWork
open OuterRampFourierWork OuterRampConvolutionWork OuterRampAverageWork
open OuterRampLengthWork OuterMaskFrequencyWork OuterBoxFourierKernelWork
open OuterSmoothStepWork OuterBufferedSourceWork OuterSourceReindexWork
open OuterSmoothErrorSupportWork LongerTupleEncoding

def cutoffKernel (X s : ℝ) (i j : ℕ) (n : Fin 9) (ξ : ℝ) : ℂ :=
  smoothedKernel 0 (cutoffLength X s i j n) (width X) (2*Real.pi*ξ)

theorem cutoffLength_pos (X s : ℝ) (hX : 2 ≤ X) (i j : ℕ) (n : Fin 9) :
    0 < cutoffLength X s i j n := by
  have hl := Real.log_nonneg (by linarith : 1 ≤ X)
  have hs := slopeMass_nonneg s i j n
  unfold cutoffLength
  positivity

theorem cutoffKernel_integrable (X s : ℝ) (hX : 2 ≤ X) (i j : ℕ) (n : Fin 9) :
    Integrable (cutoffKernel X s i j n) := by
  exact (OuterKernelIntegrableWork.kernel_integrable 0 _ _ (by unfold width; positivity)).comp_mul_left'
    (by positivity : 2*Real.pi ≠ 0)

theorem cutoff_inversion (X s : ℝ) (hX : 2 ≤ X) (r : Representation)
    (hr : r ∈ ambient X) (i j : ℕ) (n : Fin 9) :
    𝓕⁻ (cutoffKernel X s i j n)
      (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n) =
    (transition (width X)
      (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n):ℂ) := by
  unfold cutoffKernel
  rw [ramp_inversion (width X) _ (by unfold width; positivity)
    (cutoffLength_pos X s hX i j n).le]
  unfold ramp
  rw [ambient_compactRamp_eq X s hX r hr i j n]

theorem inverse_eq_phase_integral (f : ℝ → ℂ) (x : ℝ) :
    𝓕⁻ f x = ∫ξ, phase (2*Real.pi*ξ) x*f ξ := by
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [RCLike.inner_apply,conj_trivial,smul_eq_mul,phase]
  congr 2
  push_cast
  ring

theorem source_cut_integral (X s : ℝ) (hX : 2 ≤ X) (r : Representation)
    (hr : r ∈ ambient X) (i j : ℕ) (n : Fin 9) :
    (∫ξ, phase (2*Real.pi*ξ)
      (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n)*
      cutoffKernel X s i j n ξ) =
    (transition (width X)
      (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n):ℂ) := by
  rw [← inverse_eq_phase_integral]
  exact cutoff_inversion X s hX r hr i j n

theorem source_nine_integrals (X s : ℝ) (hX : 2 ≤ X) (r : Representation)
    (hr : r ∈ ambient X) (i j : ℕ) :
    (∏n : Fin 9, ∫ξ, phase (2*Real.pi*ξ)
      (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n)*
      cutoffKernel X s i j n ξ) =
    (smoothCuts (width X) (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j):ℂ) := by
  simp only [source_cut_integral X s hX r hr i j,smoothCuts,Complex.ofReal_prod]

run_cmd do
  for decl in [``cutoffLength_pos, ``cutoffKernel_integrable, ``cutoff_inversion,
      ``inverse_eq_phase_integral, ``source_cut_integral, ``source_nine_integrals] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSourceFourierWork
