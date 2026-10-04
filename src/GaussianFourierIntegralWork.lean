import GaussianMeanSquareWork
import FourierIntegralMeanSquare

/-! Gaussian smoothing removes the logarithmic loss in the continuous
Fourier mean square. All statements concern the literal integral. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace GaussianFourierIntegralWork
open GaussianMeanSquareWork CompactIntegral
open Erdos374.HarmanAnalytic151MeanSquare

def row (t u : ℝ) : ℝ := Real.sqrt Real.pi * Real.exp (-(t-u)^2/4)
def rowConstant : ℝ := Real.sqrt Real.pi * Real.sqrt (Real.pi/(1/4 : ℝ))

theorem row_bound (a b t : ℝ) : (∫ u in Icc a b, row t u) ≤ rowConstant := by
  have hi : Integrable (fun u : ℝ => Real.exp (-(t-u)^2/4)) := by
    convert (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/4)).comp_sub_left t using 1
    ext u
    congr 1
    ring
  have he : (∫ u : ℝ, Real.exp (-(t-u)^2/4)) = Real.sqrt (Real.pi/(1/4 : ℝ)) := by
    convert integral_sub_left_eq_self (fun u : ℝ => Real.exp (-(1/4 : ℝ)*u^2)) volume t using 1
    · congr 1
      ext u
      congr 1
      ring
    · exact (integral_gaussian (1/4 : ℝ)).symm
  unfold row rowConstant
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rw [← he]
  exact setIntegral_le_integral hi (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))

theorem weighted_expansion (a b : ℝ) (g : ℝ → ℂ) (hg : Continuous g) :
    ((∫ x : ℝ, weight x * ‖transform FourierIntegralMeanSquare.kernel g a b x‖^2 : ℝ) : ℂ) =
      ∫ t in Icc a b, ∫ u in Icc a b, g t * conj (g u) *
        (∫ x : ℝ, (weight x : ℂ) * exponentialKernel151 (t-u) x) := by
  let ν := volume.restrict (Icc a b)
  let H : ℝ → ℝ×ℝ → ℂ := fun x p => (weight x : ℂ) *
    (g p.1 * conj (g p.2) * exponentialKernel151 (p.1-p.2) x)
  have hw : Integrable weight := by
    convert integrable_exp_neg_mul_sq (b := (1:ℝ)) (by norm_num) using 1
    ext x
    unfold weight
    congr 1
    ring
  have hG : Integrable (fun p : ℝ×ℝ => ‖g p.1‖ * ‖g p.2‖) (ν.prod ν) :=
    hg.norm.integrableOn_Icc.mul_prod hg.norm.integrableOn_Icc
  have hH : Integrable H.uncurry (volume.prod (ν.prod ν)) := by
    apply (hw.mul_prod hG).mono'
    · exact (by dsimp [H, weight, exponentialKernel151, Function.uncurry]; fun_prop :
        Continuous H.uncurry).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro p
      dsimp [H, Function.uncurry]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        RCLike.norm_conj, norm_kernel151, mul_one]
      rw [abs_of_pos (show 0 < weight _ from Real.exp_pos _)]
  rw [← integral_complex_ofReal]
  have he (x : ℝ) : ((weight x * ‖transform FourierIntegralMeanSquare.kernel g a b x‖^2 : ℝ) : ℂ) =
      ∫ p : ℝ×ℝ, H x p ∂(ν.prod ν) := by
    rw [Complex.ofReal_mul, norm_square_expansion]
    simp only [FourierIntegralMeanSquare.kernel, kernel_mul_conj151]
    rw [← integral_const_mul]
    simp_rw [← integral_const_mul]
    exact (integral_prod (μ := ν) (ν := ν) (H x) (by
      dsimp [ν]
      rw [Measure.prod_restrict]
      exact (by dsimp [H, weight, exponentialKernel151]; fun_prop :
        Continuous (H x)).continuousOn.integrableOn_compact
          (isCompact_Icc.prod isCompact_Icc))).symm
  simp_rw [he]
  rw [integral_integral_swap hH]
  have he' (p : ℝ×ℝ) : (∫ x : ℝ, H x p) = g p.1 * conj (g p.2) *
      (∫ x : ℝ, (weight x : ℂ)*exponentialKernel151 (p.1-p.2) x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by dsimp [H]; ring)
  have hi : Integrable (fun p => ∫ x : ℝ, H x p) (ν.prod ν) := hH.integral_prod_right
  rw [integral_prod _ hi]
  simp_rw [he']
  rfl

 theorem weighted_bound (a b : ℝ) (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ x : ℝ, weight x * ‖transform FourierIntegralMeanSquare.kernel g a b x‖^2) ≤
      rowConstant * (∫ t in Icc a b, ‖g t‖^2) := by
  let K := fun ξ : ℝ => ∫ x : ℝ, (weight x : ℂ)*exponentialKernel151 ξ x
  have hK : Continuous K := by
    apply continuous_of_dominated
      (bound := fun x => weight x)
    · intro ξ
      exact (integrable_weight_kernel ξ).aestronglyMeasurable
    · intro ξ
      exact Filter.Eventually.of_forall (fun x => by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_kernel151, mul_one]
        rw [abs_of_pos (show 0 < weight _ from Real.exp_pos _)])
    · convert integrable_exp_neg_mul_sq (b := (1:ℝ)) (by norm_num) using 1
      ext x
      unfold weight
      congr 1
      ring
    · exact Filter.Eventually.of_forall (fun x => by
        unfold exponentialKernel151
        fun_prop)
  let Z : ℝ → ℝ → ℂ := fun t u => g t * conj (g u) * K (t-u)
  have hZ : Continuous Z.uncurry := by dsimp [Z]; fun_prop
  have he := congrArg norm (weighted_expansion a b g hg)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun _ => by unfold weight; positivity))] at he
  calc
    _ = ‖∫ t in Icc a b, ∫ u in Icc a b, Z t u‖ := he
    _ ≤ ∫ t in Icc a b, ‖∫ u in Icc a b, Z t u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Icc a b, ∫ u in Icc a b, ‖Z t u‖ := by
      apply integral_mono (continuous_integral a b Z hZ).norm.integrableOn_Icc
        (continuous_integral a b (fun t u => ‖Z t u‖) hZ.norm).integrableOn_Icc
      intro t
      exact norm_integral_le_integral_norm _
    _ = ∫ t in Icc a b, ∫ u in Icc a b, ‖g t‖ * ‖g u‖ * row t u := by
      simp only [Z, K, norm_mul, RCLike.norm_conj, norm_integral_weight_kernel, row]
    _ ≤ _ := IntegralSchur.quadratic_form_bound a b rowConstant g row hg
      (by unfold row Function.uncurry; fun_prop)
      (fun _ _ => by unfold row; positivity)
      (fun t u => by unfold row; congr 2; ring)
      (fun t _ => row_bound a b t)

theorem integrable_weighted_square (a b : ℝ) (g : ℝ → ℂ) (hg : Continuous g) :
    Integrable (fun x : ℝ => weight x *
      ‖transform FourierIntegralMeanSquare.kernel g a b x‖^2) := by
  have hw : Integrable weight := by
    convert integrable_exp_neg_mul_sq (b := (1:ℝ)) (by norm_num) using 1
    ext x
    unfold weight
    congr 1
    ring
  have hF := continuous_transform FourierIntegralMeanSquare.kernel g a b
    FourierIntegralMeanSquare.continuous_kernel hg
  have hnorm (x : ℝ) : ‖transform FourierIntegralMeanSquare.kernel g a b x‖ ≤
      ∫ t in Icc a b, ‖g t‖ := by
    apply (norm_integral_le_integral_norm _).trans_eq
    simp only [norm_mul, FourierIntegralMeanSquare.kernel, norm_kernel151, mul_one]
  apply (hw.mul_const ((∫ t in Icc a b, ‖g t‖)^2)).mono'
  · exact ((by unfold weight; fun_prop : Continuous weight).mul (hF.norm.pow 2)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold weight; positivity)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hnorm x) 2) (Real.exp_pos _).le

theorem unit_interval_bound (a b U : ℝ) (hU : U≤1)
    (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ x in Icc 0 U, ‖transform FourierIntegralMeanSquare.kernel g a b x‖^2) ≤
      Real.exp 1 * rowConstant * (∫ t in Icc a b, ‖g t‖^2) := by
  have hF := continuous_transform FourierIntegralMeanSquare.kernel g a b
    FourierIntegralMeanSquare.continuous_kernel hg
  have hw : Continuous weight := by unfold weight; fun_prop
  calc
    _ ≤ ∫ x in Icc 0 U, Real.exp 1 *
        (weight x * ‖transform FourierIntegralMeanSquare.kernel g a b x‖^2) := by
      apply setIntegral_mono_on (hF.norm.pow 2).integrableOn_Icc
        ((hw.mul (hF.norm.pow 2)).const_mul _).integrableOn_Icc measurableSet_Icc
      intro x hx
      have hsq : x^2≤1 := by nlinarith [hx.1,hx.2]
      have hh : 1 ≤ Real.exp 1 * weight x := by
        rw [weight, ← Real.exp_add]
        simpa using Real.exp_le_exp.mpr (show 0≤1 + -x^2 by linarith)
      change ‖transform FourierIntegralMeanSquare.kernel g a b x‖^2 ≤
        Real.exp 1 * (weight x * ‖transform FourierIntegralMeanSquare.kernel g a b x‖^2)
      nlinarith [sq_nonneg ‖transform FourierIntegralMeanSquare.kernel g a b x‖]
    _ = Real.exp 1 * (∫ x in Icc 0 U,
        weight x * ‖transform FourierIntegralMeanSquare.kernel g a b x‖^2) := integral_const_mul _ _
    _ ≤ Real.exp 1 * (∫ x : ℝ,
        weight x * ‖transform FourierIntegralMeanSquare.kernel g a b x‖^2) :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral (integrable_weighted_square a b g hg)
        (Filter.Eventually.of_forall (fun _ => by unfold weight; positivity))) (Real.exp_pos 1).le
    _ ≤ _ := (mul_le_mul_of_nonneg_left (weighted_bound a b g hg) (Real.exp_pos 1).le).trans_eq (by ring)

theorem mean_square_bound (a b c d : ℝ) (hcd : c≤d) (hlen : d-c≤1)
    (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ x in Icc c d, ‖transform FourierIntegralMeanSquare.kernel g a b x‖^2) ≤
      Real.exp 1 * rowConstant * (∫ t in Icc a b, ‖g t‖^2) := by
  let shifted : ℝ → ℂ := fun t => g t * exponentialKernel151 t c
  have hs : Continuous shifted := by dsimp [shifted, exponentialKernel151]; fun_prop
  have he (v : ℝ) : transform FourierIntegralMeanSquare.kernel g a b (v+c) =
      transform FourierIntegralMeanSquare.kernel shifted a b v := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp [shifted, FourierIntegralMeanSquare.kernel, exponentialKernel151]
    conv_rhs => rw [mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  have hchange : (∫ x in Icc c d, ‖transform FourierIntegralMeanSquare.kernel g a b x‖^2) =
      ∫ v in Icc 0 (d-c), ‖transform FourierIntegralMeanSquare.kernel shifted a b v‖^2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd]
    have hh := intervalIntegral.integral_comp_add_right
      (a := 0) (b := d-c) (fun x => ‖transform FourierIntegralMeanSquare.kernel g a b x‖^2) c
    simp only [zero_add, sub_add_cancel] at hh
    rw [← hh]
    simp_rw [he]
    rw [intervalIntegral.integral_of_le (sub_nonneg.mpr hcd), ← integral_Icc_eq_integral_Ioc]
  rw [hchange]
  have hh := unit_interval_bound a b (d-c) hlen shifted hs
  simpa only [shifted, norm_mul, norm_kernel151, mul_one] using hh

#print axioms weighted_bound
run_cmd do
  for decl in [``row_bound, ``weighted_expansion, ``weighted_bound,
      ``integrable_weighted_square, ``unit_interval_bound, ``mean_square_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end GaussianFourierIntegralWork
