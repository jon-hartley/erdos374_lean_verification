import SourceWindowFourier
import SourceAutocorrelation
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-! v9. The exact angular/standard Fourier bridge, convolution and Parseval.
UNCOMPILED DRAFT. All factors of 2*pi are explicit. No source estimate is
assumed; Parseval needs only separately verifiable qualitative regularity. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators FourierTransform
namespace SourceAngularConvolution
open SourceWindowFourier

def conv (f g : ℝ → ℂ) : ℝ → ℂ :=
  MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume

theorem conv_apply (f g : ℝ → ℂ) (u : ℝ) :
    conv f g u = ∫ v : ℝ, f v*g (u-v) := MeasureTheory.convolution_mul

theorem conv_swap (f g : ℝ → ℂ) (u : ℝ) :
    conv f g u = ∫ v : ℝ, f (u-v)*g v := MeasureTheory.convolution_mul_swap

theorem conv_integrable (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    Integrable (conv f g) :=
  MeasureTheory.Integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf hg

/-- This identity is pointwise for every frequency, including zero. -/
theorem standard_eq_angular (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = angular f (2*Real.pi*ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold angular
  apply integral_congr_ae
  filter_upwards with u
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

theorem angular_eq_standard (f : ℝ → ℂ) (t : ℝ) :
    angular f t = 𝓕 f (t/(2*Real.pi)) := by
  rw [standard_eq_angular]
  congr 1
  field_simp [Real.pi_ne_zero]

theorem angular_conv (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    angular (conv f g) t = angular f t*angular g t := by
  simp_rw [angular_eq_standard]
  exact Real.fourier_mul_convolution_eq hf hg _

theorem angular_const_mul (f : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    angular (fun u => z*f u) t = z*angular f t := by
  unfold angular
  simp_rw [show ∀ u : ℝ, Complex.exp (-Complex.I*(t:ℂ)*(u:ℂ))*(z*f u) =
    z*(Complex.exp (-Complex.I*(t:ℂ)*(u:ℂ))*f u) by intro u; ring]
  rw [integral_const_mul]

theorem angular_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i∈S, Integrable (f i)) (t : ℝ) :
    angular (fun u => ∑ i∈S, f i u) t = ∑ i∈S, angular (f i) t := by
  unfold angular
  simp only [Finset.mul_sum]
  rw [integral_finsetSum S (fun i hi => angular_integrand_integrable (f i) t (hf i hi))]

theorem angular_sub (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    angular (fun u => f u-g u) t = angular f t-angular g t := by
  unfold angular
  simp_rw [mul_sub]
  exact integral_sub (angular_integrand_integrable f t hf) (angular_integrand_integrable g t hg)

/-- Positive linear substitution with no continuity assumption on F. -/
theorem integral_scale (F : ℝ → ℝ) (c : ℝ) (hc : 0<c) :
    (∫ t : ℝ, F t) = c*(∫ ξ : ℝ, F (c*ξ)) := by
  have hd : ∀ x∈(univ:Set ℝ), HasDerivWithinAt (fun u : ℝ => c*u) c univ x := by
    intro x _
    exact (hasDerivAt_const_mul c).hasDerivWithinAt
  have hinj : Set.InjOn (fun u : ℝ => c*u) univ := by
    intro x _ y _ h
    exact (mul_left_cancel₀ hc.ne') h
  have himage : (fun u : ℝ => c*u) '' (univ:Set ℝ) = univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact ⟨y/c, Set.mem_univ _, by field_simp⟩
  have hh := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hinj F
  rw [himage] at hh
  simp only [Measure.restrict_univ] at hh
  simpa only [abs_of_pos hc, smul_eq_mul, integral_const_mul] using hh

theorem integrable_scale (F : ℝ → ℝ) (c : ℝ) (hc : 0<c) (hF : Integrable F) :
    Integrable (fun ξ => F (c*ξ)) := by
  have hd : ∀ x∈(univ:Set ℝ), HasDerivWithinAt (fun u : ℝ => c*u) c univ x := by
    intro x _
    exact (hasDerivAt_const_mul c).hasDerivWithinAt
  have hinj : Set.InjOn (fun u : ℝ => c*u) univ := by
    intro x _ y _ h
    exact (mul_left_cancel₀ hc.ne') h
  have himage : (fun u : ℝ => c*u) '' (univ:Set ℝ) = univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact ⟨y/c, Set.mem_univ _, by field_simp⟩
  have he := integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ hd hinj F
  rw [himage, integrableOn_univ, integrableOn_univ] at he
  have hi := (he.mp hF).const_mul c⁻¹
  simpa only [abs_of_pos hc, smul_eq_mul, ←mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hi

/-- Angular Parseval, obtained by the preceding ordinary inversion proof and
an explicit positive linear frequency substitution. -/
theorem angular_parseval (g : ℝ → ℂ) (B : ℝ) (hg : Measurable g)
    (hi : Integrable g) (hB : 0≤B) (hb : ∀ u, ‖g u‖≤B)
    (hc : ∀ᵐ u : ℝ, ContinuousAt g u)
    (hF : Integrable (fun t : ℝ => ‖angular g t‖^2)) :
    (∫ u : ℝ, ‖g u‖^2) = (1/(2*Real.pi))*(∫ t : ℝ, ‖angular g t‖^2) := by
  have htw : 0<2*Real.pi := by positivity
  have hstd : Integrable (fun ξ : ℝ => ‖𝓕 g ξ‖^2) := by
    simp_rw [standard_eq_angular]
    exact integrable_scale _ (2*Real.pi) htw hF
  have hp := SourceAutocorrelation.parseval g B hg hi hB hb hc hstd
  have hs := integral_scale (fun t : ℝ => ‖angular g t‖^2) (2*Real.pi) htw
  simp_rw [←standard_eq_angular] at hs
  rw [hp, hs]
  field_simp

#print axioms angular_parseval
run_cmd do
  for n in [``conv_apply, ``conv_swap, ``conv_integrable, ``standard_eq_angular,
      ``angular_eq_standard, ``angular_conv, ``angular_const_mul,
      ``angular_finset_sum, ``angular_sub, ``integral_scale,
      ``integrable_scale, ``angular_parseval] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V9 ANGULAR PARSEVAL: VALID ONLY AFTER ACTUAL COMPILATION"
end SourceAngularConvolution
