import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-!
v9. Parseval for an integrable bounded function continuous almost everywhere.
STATUS: UNCOMPILED PROOF DRAFT. The sharp function need not be continuous.
Inversion is applied to its autocorrelation. The Fourier-square integrability
premise is qualitative regularity, not a small-energy or physical-mean bound.
The actual-source instantiation is a separate module.
-/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate FourierTransform Topology
namespace SourceAutocorrelation

def reflected (g : ℝ → ℂ) (u : ℝ) : ℂ := conj (g (-u))

def correlation (g : ℝ → ℂ) : ℝ → ℂ :=
  MeasureTheory.convolution g (reflected g) (ContinuousLinearMap.mul ℂ ℂ) volume

theorem correlation_integral (g : ℝ → ℂ) (x : ℝ) :
    correlation g x = ∫ u : ℝ, g u * conj (g (u-x)) := by
  simp only [correlation, MeasureTheory.convolution_mul, reflected, neg_sub]

theorem reflected_measurable (g : ℝ → ℂ) (hg : Measurable g) :
    Measurable (reflected g) := by
  exact Complex.continuous_conj.measurable.comp (hg.comp measurable_neg)

theorem reflected_integrable (g : ℝ → ℂ) (hg : Measurable g)
    (hi : Integrable g) : Integrable (reflected g) := by
  apply hi.comp_neg.norm.mono' (reflected_measurable g hg).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => by
    simp only [reflected, Complex.norm_conj]
    exact le_rfl)

theorem correlation_integrable (g : ℝ → ℂ) (hg : Measurable g)
    (hi : Integrable g) : Integrable (correlation g) := by
  exact MeasureTheory.Integrable.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) hi (reflected_integrable g hg hi)

/-- The value at zero is proved independently of Fourier inversion. -/
theorem correlation_zero (g : ℝ → ℂ) :
    correlation g 0 = ((∫ u : ℝ, ‖g u‖^2) : ℂ) := by
  rw [correlation_integral]
  simp only [sub_zero]
  apply integral_congr_ae
  filter_upwards with u
  rw [← Complex.mul_conj']

/-- Boundedness plus L1 gives genuine L2 integrability. -/
theorem square_integrable (g : ℝ → ℂ) (B : ℝ) (hg : Measurable g)
    (hi : Integrable g) (_hB : 0 ≤ B) (hb : ∀ u, ‖g u‖ ≤ B) :
    Integrable (fun u => ‖g u‖^2) := by
  apply (hi.norm.const_mul B).mono' (hg.norm.pow_const 2).aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_right (hb u) (norm_nonneg (g u))]

/-- Dominated convergence at zero does not ask for continuity at the jumps.
The dominating function B*|g| is integrable before Parseval is used. -/
theorem correlation_continuousAt_zero (g : ℝ → ℂ) (B : ℝ)
    (hg : Measurable g) (hi : Integrable g) (_hB : 0 ≤ B)
    (hb : ∀ u, ‖g u‖ ≤ B) (hc : ∀ᵐ u : ℝ, ContinuousAt g u) :
    ContinuousAt (correlation g) 0 := by
  let F : ℝ → ℝ → ℂ := fun x u => g u * conj (g (u-x))
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable (F x) := by
    intro x
    exact (hg.mul (Complex.continuous_conj.measurable.comp
      (hg.comp (measurable_id.sub_const x)))).aestronglyMeasurable
  have hbound : ∀ x : ℝ, ∀ᵐ u : ℝ, ‖F x u‖ ≤ B*‖g u‖ := by
    intro x
    filter_upwards with u
    simp only [F, norm_mul, Complex.norm_conj]
    nlinarith [mul_le_mul_of_nonneg_left (hb (u-x)) (norm_nonneg (g u))]
  have hlim : ∀ᵐ u : ℝ, Tendsto (fun x => F x u) (𝓝 0) (𝓝 (F 0 u)) := by
    filter_upwards [hc] with u hu
    have ht : Tendsto (fun x : ℝ => u-x) (𝓝 0) (𝓝 u) := by
      have hc0 : ContinuousAt (fun x : ℝ => u-x) 0 :=
        (continuous_const.sub continuous_id).continuousAt
      simpa only [sub_zero] using hc0.tendsto
    simp only [F, sub_zero]
    exact tendsto_const_nhds.mul (Complex.continuous_conj.continuousAt.tendsto.comp
      (hu.tendsto.comp ht))
  have hh := tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => B*‖g u‖) (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall hbound) (hi.norm.const_mul B) hlim
  have heq : correlation g = fun x : ℝ => ∫ u : ℝ, F x u := by
    funext x
    exact correlation_integral g x
  change Tendsto (correlation g) (𝓝 0) (𝓝 (correlation g 0))
  rw [heq]
  exact hh

/-- Conjugate reflection, with Mathlib's ordinary Fourier convention. -/
theorem fourier_reflected (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (reflected g) ξ = conj (𝓕 g ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
  -- Use the actual standard Fourier integrand; no sign convention is implicit.
  change (∫ u : ℝ, Complex.exp (((-2*Real.pi*u*ξ:ℝ):ℂ)*Complex.I) * reflected g u) = _
  rw [← integral_neg_eq_self
    (fun u : ℝ => Complex.exp (((-2*Real.pi*u*ξ:ℝ):ℂ)*Complex.I)*reflected g u)]
  apply integral_congr_ae
  filter_upwards with u
  simp only [reflected, neg_neg, smul_eq_mul, map_mul, ← Complex.exp_conj,
    Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

theorem fourier_correlation (g : ℝ → ℂ) (hg : Measurable g)
    (hi : Integrable g) (ξ : ℝ) :
    𝓕 (correlation g) ξ = ((‖𝓕 g ξ‖^2:ℝ):ℂ) := by
  rw [correlation, Real.fourier_mul_convolution_eq hi (reflected_integrable g hg hi),
    fourier_reflected, Complex.ofReal_pow, ← Complex.mul_conj']

/-- Standard-frequency Parseval, proved by ordinary L1 inversion of the
continuous-at-zero autocorrelation, not assumed as an extra analytic input. -/
theorem parseval (g : ℝ → ℂ) (B : ℝ) (hg : Measurable g)
    (hi : Integrable g) (hB : 0 ≤ B) (hb : ∀ u, ‖g u‖ ≤ B)
    (hc : ∀ᵐ u : ℝ, ContinuousAt g u)
    (hF : Integrable (fun ξ : ℝ => ‖𝓕 g ξ‖^2)) :
    (∫ u : ℝ, ‖g u‖^2) = ∫ ξ : ℝ, ‖𝓕 g ξ‖^2 := by
  have hAi := correlation_integrable g hg hi
  have hAF : Integrable (𝓕 (correlation g)) := by
    have he : 𝓕 (correlation g) = fun ξ : ℝ => ((‖𝓕 g ξ‖^2:ℝ):ℂ) := by
      funext ξ
      exact fourier_correlation g hg hi ξ
    rw [he]
    exact hF.ofReal
  have hinv := hAi.fourierInv_fourier_eq hAF
    (correlation_continuousAt_zero g B hg hi hB hb hc)
  have hzero : 𝓕⁻ (𝓕 (correlation g)) (0:ℝ) =
      ∫ ξ : ℝ, 𝓕 (correlation g) ξ := by
    rw [Real.fourierInv_eq']
    simp
  rw [hzero, correlation_zero] at hinv
  simp_rw [fourier_correlation g hg hi] at hinv
  simp only [← Complex.ofReal_pow, integral_complex_ofReal] at hinv
  exact Complex.ofReal_injective hinv.symm

#print axioms parseval
run_cmd do
  for n in [``correlation_integral, ``reflected_measurable, ``reflected_integrable,
      ``correlation_integrable, ``correlation_zero, ``square_integrable,
      ``correlation_continuousAt_zero, ``fourier_reflected,
      ``fourier_correlation, ``parseval] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V9 AUTOCORRELATION PARSEVAL: VALID ONLY AFTER ACTUAL COMPILATION"
end SourceAutocorrelation
