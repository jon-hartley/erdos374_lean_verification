import SourceLiteralTransform
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-! v9. The measurable exponential substitution and literal physical transfer.
UNCOMPILED DRAFT. Unlike an older continuous-integrand helper, the Jacobian
formula here permits the source's sharp jumps. Parseval is constructed in the
imports, not taken as a hypothesis. No prime estimate or small source mean is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open MeasureTheory Set Filter
namespace SourcePhysicalTransfer
open SourceLiteralTransform SourceLogWindow SourceSpectralEnergy
open PositiveInteriorModel PositiveInteriorCells

theorem exponential_substitution (f : ℝ → ℝ) (X : ℝ) (hX : 0<X) :
    (∫ x in Icc X (2*X), f x) =
      ∫ u in Icc (Real.log X) (Real.log (2*X)), Real.exp u*f (Real.exp u) := by
  have hlog : Real.log X≤Real.log (2*X) := Real.log_le_log hX (by linarith)
  have hh := integral_Icc_deriv_smul_of_deriv_nonneg
    (f:=Real.exp) (f':=Real.exp) (g:=f) Real.continuous_exp.continuousOn
    (fun u _ => Real.hasDerivAt_exp u) (fun u _ => (Real.exp_pos u).le) hlog
  simpa only [smul_eq_mul, Real.exp_log hX, Real.exp_log (show 0<2*X by positivity)] using hh.symm

theorem exponential_interval (X u : ℝ) (hX : 0<X)
    (hu : u∈Icc (Real.log X) (Real.log (2*X))) :
    Real.exp u∈Icc X (2*X) := by
  constructor
  · simpa only [Real.exp_log hX] using Real.exp_le_exp.mpr hu.1
  · simpa only [Real.exp_log (show 0<2*X by positivity)] using Real.exp_le_exp.mpr hu.2

/-- This generic inequality allows measurable jump discontinuities in g.
Its square-integrability premise is qualitative, not a desired energy estimate. -/
theorem physical_bound (f : ℝ → ℝ) (g : ℝ → ℂ) (X : ℝ) (hX : 0<X)
    (hg : Measurable g) (hi : Integrable (fun u => ‖g u‖^2))
    (he : ∀ x∈Icc X (2*X), g (Real.log x)=((f x/x:ℝ):ℂ)) :
    (∫ x in Icc X (2*X), (f x)^2)/X ≤ 8*X^2*(∫ u : ℝ, ‖g u‖^2) := by
  let S := Icc (Real.log X) (Real.log (2*X))
  let w : ℝ → ℝ := fun u => (Real.exp u)^3/X*‖g u‖^2
  have hweight (u : ℝ) (hu : u∈S) : (Real.exp u)^3/X≤8*X^2 := by
    have hx := exponential_interval X u hX hu
    apply (div_le_iff₀ hX).mpr
    have hh := pow_le_pow_left₀ (Real.exp_pos u).le hx.2 3
    nlinarith
  have hwmeas : Measurable w := by dsimp [w]; fun_prop
  have hwi : IntegrableOn w S := by
    apply (hi.integrableOn.const_mul (8*X^2)).mono' hwmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ w u by dsimp [w]; positivity)]
    exact mul_le_mul_of_nonneg_right (hweight u hu) (sq_nonneg _)
  have hpoint (u : ℝ) (hu : u∈S) :
      Real.exp u*(f (Real.exp u))^2/X=w u := by
    have hx := exponential_interval X u hX hu
    have hr := he (Real.exp u) hx
    rw [Real.log_exp] at hr
    dsimp [w]
    rw [hr, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
    field_simp <;> ring
  have hident : (∫ x in Icc X (2*X), (f x)^2)/X=∫ u in S, w u := by
    rw [exponential_substitution (fun x => (f x)^2) X hX, ←integral_div]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact hpoint u hu
  have hm := setIntegral_mono_on hwi (hi.integrableOn.const_mul (8*X^2))
    measurableSet_Icc (fun u hu => mul_le_mul_of_nonneg_right (hweight u hu) (sq_nonneg _))
  rw [integral_const_mul] at hm
  have hs : (∫ u in S, ‖g u‖^2)≤∫ u : ℝ, ‖g u‖^2 := by
    have hh := setIntegral_mono_set hi.integrableOn
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall (show S⊆(univ:Set ℝ) from subset_univ _))
    simpa only [Measure.restrict_univ] using hh
  rw [hident]
  exact hm.trans (mul_le_mul_of_nonneg_left hs (by positivity))

/-- Exact full source Fourier-to-physical theorem. There is no external
arithmetic cap, local PNT error, Parseval assumption or source-mean assumption. -/
theorem raw_second_mean_le_spectral (X Y : ℝ) (j : ℕ×ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hY : 0<Y) (hYX : Y≤X/2) :
    (∫ x in Icc X (2*X), (SourceRawMean.rawDelta X Y j x)^2)/X ≤
      (8*X^2/(2*Real.pi))*(∫ t : ℝ, spectralDensity X (Y/X) j t) := by
  have hXp : 0<X := by linarith
  have hδ : 0<Y/X ∧ Y/X<1 := ⟨div_pos hY hXp,(div_lt_one hXp).mpr (by linarith)⟩
  have hρ : 0<1-Y/X ∧ 1-Y/X<1 := by constructor <;> linarith [hδ.1,hδ.2]
  have hi := SourceAutocorrelation.square_integrable (profile X j (1-Y/X))
    (profileCap X j) (profile_measurable X _ j)
    (profile_integrable X _ j hXp hρ.1 hρ.2) (profileCap_nonneg X j)
    (fun u => profile_norm_le X _ u j hXp)
  have hp := physical_bound (SourceRawMean.rawDelta X Y j) (profile X j (1-Y/X)) X hXp
    (profile_measurable X _ j) hi (by
      intro x hx
      exact congrArg (fun y : ℝ => (y:ℂ)) (centered_eq_raw X x Y j hXp hx hY hYX))
  rw [profile_parseval X Y j hX hlog hj hY hYX] at hp
  convert hp using 1 <;> ring

/-- Normalization by the actual width is an exact identity; no factor of X
or factor two from the half-width is silently changed. -/
theorem normalized_raw_le_spectral (X Y : ℝ) (j : ℕ×ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hY : 0<Y) (hYX : Y≤X/2) :
    (∫ x in Icc X (2*X), (SourceRawMean.rawDelta X Y j x)^2)/(X*Y^2) ≤
      (4/Real.pi)*((∫ t : ℝ, spectralDensity X (Y/X) j t)/(Y/X)^2) := by
  have hh := div_le_div_of_nonneg_right
    (raw_second_mean_le_spectral X Y j hX hlog hj hY hYX) (sq_nonneg Y)
  convert hh using 1 <;> field_simp <;> ring

#print axioms raw_second_mean_le_spectral
run_cmd do
  for n in [``exponential_substitution,``exponential_interval,``physical_bound,
      ``raw_second_mean_le_spectral,``normalized_raw_le_spectral] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V9 ACTUAL PHYSICAL TRANSFER: VALID ONLY AFTER ACTUAL COMPILATION"
end SourcePhysicalTransfer
