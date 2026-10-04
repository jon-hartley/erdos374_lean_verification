import FourierIntegralMeanSquare
import LogIntegralTransfer

/-!
Mean square of the actual complex-power integral on a vertical line.
This uses the Fourier estimate and the full logarithmic substitution,
with the endpoint weight shown explicitly.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set

namespace MellinIntegralMeanSquare
open Erdos374.HarmanAnalytic151MeanSquare

def transform (g : ℝ → ℂ) (a b σ x : ℝ) : ℂ :=
  ∫ t in Icc a b, g t * (x : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ))

theorem power_factor (x σ t : ℝ) (hx : 0 < x) :
    (x : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) =
      ((x ^ σ : ℝ) : ℂ) * FourierIntegralMeanSquare.kernel (Real.log x) t := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.cpow_add _ _ hxC, ← Complex.ofReal_cpow hx.le,
    Complex.cpow_def_of_ne_zero hxC, ← Complex.ofReal_log hx.le]
  unfold FourierIntegralMeanSquare.kernel exponentialKernel151
  congr 2
  ring

theorem transform_factor (g : ℝ → ℂ) (a b σ x : ℝ) (hx : 0 < x) :
    transform g a b σ x = ((x ^ σ : ℝ) : ℂ) *
      CompactIntegral.transform FourierIntegralMeanSquare.kernel g a b
        (Real.log x) := by
  unfold transform CompactIntegral.transform
  simp_rw [power_factor x σ _ hx]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

theorem norm_square (g : ℝ → ℂ) (a b σ x : ℝ) (hx : 0 < x) :
    ‖transform g a b σ x‖ ^ 2 = x ^ (2 * σ) *
      ‖CompactIntegral.transform FourierIntegralMeanSquare.kernel g a b
        (Real.log x)‖ ^ 2 := by
  rw [transform_factor g a b σ x hx, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx.le σ)]
  congr 1
  rw [show 2 * σ = σ * (2 : ℝ) by ring, Real.rpow_mul hx.le, Real.rpow_two]

theorem endpoint_bound (X σ a b : ℝ) (hX : 0 < X) (hσ : 0 ≤ σ)
    (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ x in Icc X (2 * X), ‖transform g a b σ x‖ ^ 2) ≤
      (2 * X) ^ (2 * σ + 1) * (8 * Real.log (1 + b - a)) *
        ∫ t in Icc a b, ‖g t‖ ^ 2 := by
  let F := CompactIntegral.transform FourierIntegralMeanSquare.kernel g a b
  have hF : Continuous F := CompactIntegral.continuous_transform
    FourierIntegralMeanSquare.kernel g a b FourierIntegralMeanSquare.continuous_kernel hg
  have hXY : X ≤ 2 * X := by linarith
  have hlogs : Real.log X ≤ Real.log (2 * X) := Real.log_le_log hX hXY
  have hlen : Real.log (2 * X) - Real.log X ≤ 1 := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX.ne']
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc
    _ = ∫ x in Icc X (2 * X), x ^ (2 * σ) * ‖F (Real.log x)‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact norm_square g a b σ x (hX.trans_le hx.1)
    _ ≤ (2 * X) ^ (2 * σ + 1) *
        ∫ v in Icc (Real.log X) (Real.log (2 * X)), ‖F v‖ ^ 2 :=
      LogIntegralTransfer.weighted_bound X (2 * X) σ hX hXY hσ F hF
    _ ≤ (2 * X) ^ (2 * σ + 1) *
        ((8 * Real.log (1 + b - a)) * ∫ t in Icc a b, ‖g t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (FourierIntegralMeanSquare.mean_square_bound a b (Real.log X)
          (Real.log (2 * X)) hlogs hlen g hg) (by positivity)
    _ = _ := by ring

end MellinIntegralMeanSquare

#print axioms MellinIntegralMeanSquare.endpoint_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``MellinIntegralMeanSquare.endpoint_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "MELLIN INTEGRAL MEAN SQUARE PASSED"
