import IntegralTransformBound
import ReciprocalDistanceKernel

/-!
An explicit mean-square bound for continuous Fourier integrals on an
interval of length at most one. This supplies the Fourier step in the
Mellin mean-square transfer used in Harman's Lemma 2.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate

namespace FourierIntegralMeanSquare
open Erdos374.HarmanAnalytic151MeanSquare CompactIntegral

def kernel (x t : ℝ) : ℂ := exponentialKernel151 t x

theorem continuous_kernel : Continuous kernel.uncurry := by
  unfold kernel exponentialKernel151 Function.uncurry
  fun_prop

theorem correlation_eq (c d t u : ℝ) (hcd : c ≤ d) :
    correlation kernel c d t u =
      ∫ x in c..d, exponentialKernel151 (t - u) x := by
  unfold correlation kernel
  simp_rw [kernel_mul_conj151]
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hcd]

theorem correlation_bound (c d : ℝ) (hcd : c ≤ d) (hlen : d - c ≤ 1)
    (t u : ℝ) :
    ‖correlation kernel c d t u‖ ≤
      4 * ReciprocalDistanceKernel.kernel t u := by
  rw [correlation_eq c d t u hcd]
  have htrivial : ‖∫ x in c..d, exponentialKernel151 (t - u) x‖ ≤ 1 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c) (b := d) (C := (1 : ℝ))
      (f := exponentialKernel151 (t - u)) (fun x _ => by rw [norm_kernel151])
    rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hcd)] at hh
    exact hh.trans hlen
  unfold ReciprocalDistanceKernel.kernel
  have hp : 0 < 1 + |t - u| := by positivity
  by_cases hsmall : |t - u| ≤ 1
  · apply htrivial.trans
    rw [← div_eq_mul_inv, le_div_iff₀ hp]
    linarith
  · have hd : 0 < |t - u| := by linarith
    have hne : t - u ≠ 0 := abs_pos.mp hd
    apply (norm_integral_kernel_le151 (t - u) c d hne).trans
    rw [← div_eq_mul_inv, div_le_div_iff₀ hd hp]
    linarith

theorem mean_square_bound (a b c d : ℝ)
    (hcd : c ≤ d) (hlen : d - c ≤ 1)
    (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ x in Icc c d, ‖transform kernel g a b x‖ ^ 2) ≤
      (8 * Real.log (1 + b - a)) * ∫ t in Icc a b, ‖g t‖ ^ 2 := by
  let H : ℝ → ℝ → ℝ := fun t u => 4 * ReciprocalDistanceKernel.kernel t u
  apply IntegralTransformBound.mean_square_le a b c d
    (8 * Real.log (1 + b - a)) kernel g H continuous_kernel hg
  · exact continuous_const.mul ReciprocalDistanceKernel.continuous_kernel
  · intro t u
    exact mul_nonneg (by norm_num) (ReciprocalDistanceKernel.nonnegative t u)
  · intro t u
    dsimp [H]
    rw [ReciprocalDistanceKernel.symmetric]
  · exact correlation_bound c d hcd hlen
  · intro t ht
    dsimp [H]
    rw [integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left
      (ReciprocalDistanceKernel.row_bound a b t ht) (by norm_num : (0 : ℝ) ≤ 4)
    linarith

end FourierIntegralMeanSquare

#print axioms FourierIntegralMeanSquare.mean_square_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``FourierIntegralMeanSquare.mean_square_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOURIER INTEGRAL MEAN SQUARE PASSED"
