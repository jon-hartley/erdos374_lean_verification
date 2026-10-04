import Item1SelectedFourier
import SourcePhysicalTransfer
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! UNCOMPILED, 2026-10-02. The log profile is ALREADY divided by eta.
Thus g(log x)=r(x), not rawDelta(x)/x. This distinction puts ell^2 in the
DENOMINATOR of the all-cell first-mean transfer. Measurable sharp jumps are
allowed; qualitative L2 integrability is constructed before estimating it.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open MeasureTheory Set Filter
namespace Item1NormalizedPhysical
open Item1SelectedWindow Item1SelectedFourier SourcePhysicalTransfer
open PositiveInteriorModel PositiveInteriorCells CancellationTransferEndpoints

/-- Qualitative physical-square integrability, with no small-energy premise. -/
theorem physical_square_integrable (r : ℝ → ℝ) (g : ℝ → ℂ) (X : ℝ)
    (hX : 0<X) (hg : Measurable g) (hi : Integrable (fun u => ‖g u‖^2))
    (he : ∀ x∈Icc X (2*X), g (Real.log x)=(r x:ℂ)) :
    IntegrableOn (fun x => (r x)^2) (Icc X (2*X)) := by
  let A := Icc (Real.log X) (Real.log (2*X))
  let w := fun u : ℝ => Real.exp u*‖g u‖^2
  have hwm : Measurable w := by dsimp [w]; fun_prop
  have hwi : IntegrableOn w A := by
    apply (hi.integrableOn.const_mul (2*X)).mono' hwm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ w u by dsimp [w]; positivity)]
    exact mul_le_mul_of_nonneg_right (exponential_interval X u hX hu).2 (sq_nonneg _)
  have hcomp : IntegrableOn (fun u => Real.exp u*(r (Real.exp u))^2) A := by
    apply hwi.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hh := he (Real.exp u) (exponential_interval X u hX hu)
    rw [Real.log_exp] at hh
    simp only [w,hh,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hlog : Real.log X≤Real.log (2*X) := Real.log_le_log hX (by linarith)
  have hjac := integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg
    (f:=Real.exp) (f':=Real.exp) (g:=fun x => (r x)^2)
    Real.continuous_exp.continuousOn (fun u _ => Real.hasDerivAt_exp u)
    (fun u _ => (Real.exp_pos u).le) hlog
  simpa only [smul_eq_mul,Real.exp_log hX,
    Real.exp_log (show 0<2*X by positivity)] using hjac.mp hcomp

/-- The correct normalized transfer: dx/X is at most 2 du. -/
theorem physical_square_le (r : ℝ → ℝ) (g : ℝ → ℂ) (X : ℝ)
    (hX : 0<X) (hg : Measurable g) (hi : Integrable (fun u => ‖g u‖^2))
    (he : ∀ x∈Icc X (2*X), g (Real.log x)=(r x:ℂ)) :
    (∫ x in Icc X (2*X), (r x)^2)/X ≤ 2*(∫ u : ℝ, ‖g u‖^2) := by
  let A := Icc (Real.log X) (Real.log (2*X))
  let w := fun u : ℝ => (Real.exp u/X)*‖g u‖^2
  have hweight (u : ℝ) (hu : u∈A) : Real.exp u/X≤2 :=
    (div_le_iff₀ hX).mpr (exponential_interval X u hX hu).2
  have hwm : Measurable w := by dsimp [w]; fun_prop
  have hwi : IntegrableOn w A := by
    apply (hi.integrableOn.const_mul 2).mono' hwm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ w u by dsimp [w]; positivity)]
    exact mul_le_mul_of_nonneg_right (hweight u hu) (sq_nonneg _)
  have hid : (∫ x in Icc X (2*X), (r x)^2)/X = ∫ u in A, w u := by
    rw [exponential_substitution (fun x => (r x)^2) X hX,←integral_div]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hh := he (Real.exp u) (exponential_interval X u hX hu)
    rw [Real.log_exp] at hh
    simp only [w,hh,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    ring
  have hm := setIntegral_mono_on hwi (hi.integrableOn.const_mul 2)
    measurableSet_Icc (fun u hu => mul_le_mul_of_nonneg_right (hweight u hu) (sq_nonneg _))
  rw [integral_const_mul] at hm
  have hs : (∫ u in A, ‖g u‖^2)≤∫ u : ℝ, ‖g u‖^2 := by
    have hh := setIntegral_mono_set hi.integrableOn
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall (show A⊆(univ:Set ℝ) from subset_univ _))
    simpa only [Measure.restrict_univ] using hh
  rw [hid]
  exact hm.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

theorem selectedResidual_square_integrable (X Y : ℝ) (j : ℕ × ℕ)
    (S : Finset SourceTriple) (hS : S⊆sourceCoordinates X j)
    (hX : 0<X) (hY : 0<Y) (hYX : Y≤X/2) :
    IntegrableOn (fun x => (selectedResidual X Y j S x)^2) (Icc X (2*X)) :=
  physical_square_integrable _ _ X hX (normalizedProfile_measurable X Y j S)
    (normalizedProfile_square_integrable X Y j S hX hY hYX)
    (fun x hx => normalizedProfile_log X x Y j S hS hX hx hY hYX)

/-- Source-specific normalized second mean. No raw second mean, prime cap,
low-frequency estimate, or Parseval assertion occurs among its arguments. -/
theorem selected_second_mean (X Y : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (hS : S⊆sourceCoordinates X j) (hX : 2≤X) (hlog : 1000000≤Real.log X)
    (hj : j∈boxes (mesh X)) (hY : 0<Y) (hYX : Y≤X/2) :
    (∫ x in Icc X (2*X), (selectedResidual X Y j S x)^2)/X ≤ energy X Y j S/Real.pi := by
  have hXp : 0<X := by linarith
  have hh := physical_square_le (selectedResidual X Y j S) (normalizedProfile X Y j S)
    X hXp (normalizedProfile_measurable X Y j S)
    (normalizedProfile_square_integrable X Y j S hXp hY hYX)
    (fun x hx => normalizedProfile_log X x Y j S hS hXp hx hY hYX)
  rw [normalized_parseval X Y j S hX hlog hj hY hYX] at hh
  convert hh using 1 <;> field_simp <;> ring

/-- Regularity of the absolute first mean is established independently. -/
theorem selectedResidual_integrable (X Y : ℝ) (j : ℕ × ℕ)
    (S : Finset SourceTriple) (hS : S⊆sourceCoordinates X j)
    (hX : 0<X) (hY : 0<Y) (hYX : Y≤X/2) :
    IntegrableOn (selectedResidual X Y j S) (Icc X (2*X)) := by
  let f : ℝ → ℝ := fun x => (normalizedProfile X Y j S (Real.log x)).re
  have hf : Measurable f :=
    Complex.continuous_re.measurable.comp
      ((normalizedProfile_measurable X Y j S).comp Real.measurable_log)
  have hi : IntegrableOn f (Icc X (2*X)) := by
    apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne hf.aestronglyMeasurable
      (M := profileBound X j S/(Y/X))
    filter_upwards with x
    exact (Complex.abs_re_le_norm _).trans (normalizedProfile_bound X Y (Real.log x) j S hX hY)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp only [f,normalizedProfile_log X x Y j S hS hX hx hY hYX,Complex.ofReal_re]

end Item1NormalizedPhysical


run_cmd do
  for target in [``Item1NormalizedPhysical.physical_square_integrable,
    ``Item1NormalizedPhysical.physical_square_le,
    ``Item1NormalizedPhysical.selectedResidual_square_integrable,
    ``Item1NormalizedPhysical.selected_second_mean,
    ``Item1NormalizedPhysical.selectedResidual_integrable] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
