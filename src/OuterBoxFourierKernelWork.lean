import OuterMaskFrequencyWork
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Fourier kernels of a finite interval and its uniform smoothing.
Pointwise bounds supply the constant / inverse-frequency / inverse-square
majorants needed for a logarithmic separator cost. Fourier inversion and
identification with the source ramp are not asserted in this module. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace OuterBoxFourierKernelWork
open OuterMaskFrequencyWork

def boxKernel (a b t : ℝ) : ℂ := ∫x in a..b, phase (-t) x

theorem boxKernel_formula (a b t : ℝ) (ht : t ≠ 0) :
    boxKernel a b t = (phase (-t) b-phase (-t) a)/(Complex.I*(-t:ℝ)) := by
  have hc : Complex.I * (-t:ℝ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by
    exact_mod_cast neg_ne_zero.mpr ht)
  simpa [boxKernel,phase,mul_assoc] using
    (integral_exp_mul_complex (a := a) (b := b) hc)

theorem boxKernel_length (a b t : ℝ) : ‖boxKernel a b t‖ ≤ |b-a| := by
  simpa only [one_mul,boxKernel] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := 1) (fun x _ => (phase_norm (-t) x).le))

theorem boxKernel_decay (a b t : ℝ) (ht : t ≠ 0) :
    ‖boxKernel a b t‖ ≤ 2/|t| := by
  rw [boxKernel_formula a b t ht,norm_div]
  have hn : ‖Complex.I*(-t:ℝ)‖ = |t| := by simp [norm_mul]
  rw [hn]
  apply div_le_div_of_nonneg_right _ (abs_nonneg t)
  simpa only [phase_norm, show (1:ℝ)+1=2 by norm_num] using norm_sub_le (phase (-t) b) (phase (-t) a)

def smoothedKernel (a b δ t : ℝ) : ℂ :=
  boxKernel a b t * boxKernel (-δ) δ t / (2*δ:ℝ)

theorem averagingKernel_norm (δ t : ℝ) (hδ : 0 < δ) :
    ‖boxKernel (-δ) δ t / (2*δ:ℝ)‖ ≤ 1 := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 2*δ)]
  apply (div_le_one (by positivity)).mpr
  simpa [sub_neg_eq_add, ← two_mul, abs_of_pos (by positivity : 0 < 2*δ)] using boxKernel_length (-δ) δ t

theorem smoothedKernel_length (a b δ t : ℝ) (hδ : 0 < δ) :
    ‖smoothedKernel a b δ t‖ ≤ |b-a| := by
  calc
    _ = ‖boxKernel a b t‖ * ‖boxKernel (-δ) δ t/(2*δ:ℝ)‖ := by
      rw [smoothedKernel,mul_div_assoc,norm_mul]
    _ ≤ |b-a| * 1 := mul_le_mul (boxKernel_length a b t)
      (averagingKernel_norm δ t hδ) (norm_nonneg _) (abs_nonneg _)
    _ = _ := mul_one _

theorem smoothedKernel_first_decay (a b δ t : ℝ) (hδ : 0 < δ) (ht : t ≠ 0) :
    ‖smoothedKernel a b δ t‖ ≤ 2/|t| := by
  calc
    _ = ‖boxKernel a b t‖ * ‖boxKernel (-δ) δ t/(2*δ:ℝ)‖ := by
      rw [smoothedKernel,mul_div_assoc,norm_mul]
    _ ≤ (2/|t|)*1 := mul_le_mul (boxKernel_decay a b t ht)
      (averagingKernel_norm δ t hδ) (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

theorem smoothedKernel_second_decay (a b δ t : ℝ) (hδ : 0 < δ) (ht : t ≠ 0) :
    ‖smoothedKernel a b δ t‖ ≤ 2/(δ*t^2) := by
  rw [smoothedKernel,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2*δ)]
  calc
    _ ≤ ((2/|t|)*(2/|t|))/(2*δ) := div_le_div_of_nonneg_right
      (mul_le_mul (boxKernel_decay a b t ht) (boxKernel_decay (-δ) δ t ht)
        (norm_nonneg _) (by positivity)) (by positivity)
    _ = _ := by rw [div_mul_div_comm]; rw [← sq_abs]; field_simp

run_cmd do
  for decl in [``boxKernel_formula, ``boxKernel_length, ``boxKernel_decay,
      ``averagingKernel_norm, ``smoothedKernel_length, ``smoothedKernel_first_decay,
      ``smoothedKernel_second_decay] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBoxFourierKernelWork
