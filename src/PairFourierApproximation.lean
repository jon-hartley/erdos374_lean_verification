import PairFourierResidual
import PairProjectionEnergy
import Mathlib.Algebra.Order.Chebyshev

/-! Quantitative finite approximation of the actual signed divisor sum. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set intervalIntegral
open scoped Real ENNReal BigOperators

namespace PairFourierApproximation

def polynomial (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) (F : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 Q, (a n : ℂ) *
    (if hn : 0 < n then PairFourier.hardProjection n hn h F x else 0)

def singleError (n : ℕ) (h : ℝ) (F : ℕ) (x : ℝ) : ℂ :=
  PairFourier.discrepancy n h x -
    (if hn : 0 < n then PairFourier.hardProjection n hn h F x else 0)

theorem singleError_pos (n : ℕ) (hn : 0 < n) (h : ℝ) (F : ℕ) (x : ℝ) :
    singleError n h F x =
      PairFourier.discrepancy n h x - PairFourier.hardProjection n hn h F x := by
  simp only [singleError, dite_eq_left hn]

theorem polynomial_continuous (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) (F : ℕ) :
    Continuous (polynomial Q a h F) := by
  unfold polynomial
  apply continuous_finsetSum
  intro n hn
  have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  simp only [dite_eq_left hn0, PairFourier.hardProjection]
  exact continuous_const.mul (PairFourier.projection_continuous _ _ _ _)

theorem polynomial_memLp (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) (F : ℕ)
    (L R : ℝ) (p : ℝ≥0∞) :
    MemLp (polynomial Q a h F) p (volume.restrict (Ioc L R)) := by
  unfold polynomial
  apply memLp_finsetSum
  intro n hn
  have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  simp only [dite_eq_left hn0, PairFourier.hardProjection]
  exact (PairFourier.projection_memLp _ _ _ _ L R p).const_mul (a n : ℂ)

theorem difference_eq_sum (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) (F : ℕ) (x : ℝ) :
    PairProjectionEnergy.remainder Q a h x - polynomial Q a h F x =
      ∑ n ∈ Finset.Icc 1 Q, (a n : ℂ) * singleError n h F x := by
  unfold PairProjectionEnergy.remainder SingletonResidueVariance.remainder polynomial
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  unfold singleError PairFourier.discrepancy
  ring

theorem singleError_memLp (n : ℕ) (h : ℝ) (F : ℕ) (L R : ℝ) (p : ℝ≥0∞) :
    MemLp (singleError n h F) p (volume.restrict (Ioc L R)) := by
  change MemLp (fun x => PairFourier.discrepancy n h x -
    (if hn : 0 < n then PairFourier.hardProjection n hn h F x else 0)) p _
  by_cases hn : 0 < n
  · simp only [dite_eq_left hn]
    exact PairFourier.discrepancy_residual_memLp n hn h F L R p
  · simp only [dite_eq_right hn, sub_zero]
    exact PairFourier.discrepancy_memLp n h L R p

theorem singleError_square_integrable (n : ℕ) (h : ℝ) (F : ℕ) (L R : ℝ) :
    IntervalIntegrable (fun x => ‖singleError n h F x‖^2) volume L R := by
  constructor <;> exact (singleError_memLp n h F _ _ 2).integrable_norm_pow (by norm_num)

theorem difference_square_integrable (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) (F : ℕ) (L R : ℝ) :
    IntervalIntegrable
      (fun x => ‖PairProjectionEnergy.remainder Q a h x - polynomial Q a h F x‖^2)
      volume L R := by
  constructor <;> exact ((PairProjectionEnergy.remainder_memLp Q a h _ _).sub
    (polynomial_memLp Q a h F _ _ 2)).integrable_norm_pow (by norm_num)

theorem pointwise_error_le (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) (F : ℕ) (B x : ℝ)
    (_hB : 0 ≤ B) (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    ‖PairProjectionEnergy.remainder Q a h x - polynomial Q a h F x‖^2 ≤
      (Q:ℝ) * B^2 * (∑ n ∈ Finset.Icc 1 Q, ‖singleError n h F x‖^2) := by
  rw [difference_eq_sum]
  have hc : (Finset.Icc 1 Q).card = Q := by simp
  calc
    _ ≤ (∑ n ∈ Finset.Icc 1 Q, ‖(a n:ℂ)*singleError n h F x‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ ((Finset.Icc 1 Q).card:ℝ) *
        (∑ n ∈ Finset.Icc 1 Q, ‖(a n:ℂ)*singleError n h F x‖^2) :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ (Q:ℝ) * (∑ n ∈ Finset.Icc 1 Q, B^2*‖singleError n h F x‖^2) := by
      rw [hc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Q)
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (ha n hn) 2)
        (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- All approximation errors are paid over the whole interval. Coefficients
remain signed; only this quadratic upper estimate takes their absolute values. -/
theorem integral_error_le (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) (F : ℕ) (hF : 0 < F)
    (B t T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (∫ x in t..t+T,
      ‖PairProjectionEnergy.remainder Q a h x - polynomial Q a h F x‖^2) ≤
      (4 * B^2 * (Q:ℝ) / F) * (T * SingletonHarmonic.harmonicSum Q + Q) := by
  have his : IntervalIntegrable (fun x => ∑ n ∈ Finset.Icc 1 Q,
      ‖singleError n h F x‖^2) volume t (t+T) := by
    constructor <;> exact MeasureTheory.integrable_finsetSum _
      (fun n _ => (singleError_memLp n h F _ _ 2).integrable_norm_pow (by norm_num))
  calc
    _ ≤ ∫ x in t..t+T,
        (Q:ℝ)*B^2*(∑ n ∈ Finset.Icc 1 Q, ‖singleError n h F x‖^2) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (difference_square_integrable Q a h F t (t+T)) (his.const_mul _)
      intro x _
      exact pointwise_error_le Q a h F B x hB ha
    _ = (Q:ℝ)*B^2 * (∑ n ∈ Finset.Icc 1 Q,
        ∫ x in t..t+T, ‖singleError n h F x‖^2) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
      intro n _
      exact singleError_square_integrable n h F t (t+T)
    _ ≤ (Q:ℝ)*B^2 * (∑ n ∈ Finset.Icc 1 Q, (4/(F:ℝ)) * (T/n+1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
      simp only [singleError_pos n hn0]
      exact PairFourier.hard_residual_interval_bound n hn0 h F hF t T hT
    _ = _ := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel,
        div_eq_mul_inv, ← Finset.mul_sum, SingletonHarmonic.harmonicSum, one_mul]
      ring

end PairFourierApproximation
