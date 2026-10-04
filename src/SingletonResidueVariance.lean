import SingletonPair
import SingletonHarmonic

/-! The fixed-width second moment for arbitrary real signed divisor coefficients. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SingletonResidueVariance

def remainder (Q : ℕ) (a : ℕ → ℝ) (x h : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Q, a n * SingletonDivisor.discrepancy n x h

theorem square_eq_sum (Q : ℕ) (a : ℕ → ℝ) (x h : ℝ) :
    remainder Q a x h ^ 2 =
      ∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
        (a m * a n) * (SingletonDivisor.discrepancy m x h *
          SingletonDivisor.discrepancy n x h) := by
  rw [remainder, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem square_intervalIntegrable (Q : ℕ) (a : ℕ → ℝ) (h L R : ℝ) :
    IntervalIntegrable (fun x => remainder Q a x h ^ 2) volume L R := by
  simp_rw [square_eq_sum]
  convert IntervalIntegrable.sum (Finset.Icc 1 Q) (fun m _ =>
      IntervalIntegrable.sum (Finset.Icc 1 Q) (fun n _ =>
        (SingletonCovariance.product_integrable m n h L R).const_mul (a m * a n))) using 1
  funext x
  simp only [Finset.sum_apply]

theorem integral_square_eq_sum (Q : ℕ) (a : ℕ → ℝ) (h L R : ℝ) :
    (∫ x in L..R, remainder Q a x h ^ 2) =
      ∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
        (a m * a n) * (∫ x in L..R,
          SingletonDivisor.discrepancy m x h * SingletonDivisor.discrepancy n x h) := by
  have hi : ∀ m ∈ Finset.Icc 1 Q, ∀ n ∈ Finset.Icc 1 Q,
      IntervalIntegrable (fun x => (a m * a n) *
        (SingletonDivisor.discrepancy m x h * SingletonDivisor.discrepancy n x h))
        volume L R := by
    intro m hm n hn
    exact (SingletonCovariance.product_integrable m n h L R).const_mul (a m * a n)
  simp_rw [square_eq_sum]
  rw [intervalIntegral.integral_finsetSum
    (fun m hm => by
      convert IntervalIntegrable.sum (Finset.Icc 1 Q) (fun n hn => hi m hm n hn) using 1
      funext x
      simp only [Finset.sum_apply])]
  apply Finset.sum_congr rfl
  intro m hm
  rw [intervalIntegral.integral_finsetSum (fun n hn => hi m hm n hn)]
  simp_rw [intervalIntegral.integral_const_mul]

/-- Unconditional fixed-width variance with the physical support bound `Q`.
The coefficients can have arbitrary signs; their absolute values enter only in
the upper bound after expanding the exact square. -/
theorem integral_square_le (Q : ℕ) (a : ℕ → ℝ) (B h t T : ℝ)
    (hB : 0 ≤ B) (hh : 0 ≤ h) (hT : 0 ≤ T)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (∫ x in t..t + T, remainder Q a x h ^ 2) ≤
      B ^ 2 * (T * h * SingletonHarmonic.harmonicSum Q ^ 3 + 2 * (Q : ℝ) ^ 4) := by
  rw [integral_square_eq_sum]
  apply le_trans _ (SingletonHarmonic.weighted_product_pair_bound Q a B T h hB hT hh ha)
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro n hn
  have hm0 : 0 < m := lt_of_lt_of_le (by omega) (Finset.mem_Icc.mp hm).1
  have hn0 : 0 < n := lt_of_lt_of_le (by omega) (Finset.mem_Icc.mp hn).1
  have hp := SingletonPair.integral_abs_le m n hm0 hn0 h t T hh hT
  calc
    _ ≤ |(a m * a n) * (∫ x in t..t + T,
        SingletonDivisor.discrepancy m x h * SingletonDivisor.discrepancy n x h)| :=
      le_abs_self _
    _ = |a m * a n| * |∫ x in t..t + T,
        SingletonDivisor.discrepancy m x h * SingletonDivisor.discrepancy n x h| := abs_mul _ _
    _ ≤ |a m * a n| *
        (T * h * (Nat.gcd m n : ℝ) / ((m : ℝ) * n) + 2 * (m : ℝ) * n) :=
      mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ = |a m * a n| *
        (T * h * ((Nat.gcd m n : ℝ) / ((m : ℝ) * n)) + 2 * ((m : ℝ) * n)) := by ring

end SingletonResidueVariance
