import PairSpacingProjectionSum
import PairFourierApproximation

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos374.PairSpacingPolynomial

open PairSpacingRational PairSpacingKernel PairSpacingMeanSquare PairSpacingCollectedEnergy PairFourier

theorem polynomial_eq_representative_sum (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) (F : ℕ) (x : ℝ) :
    PairFourierApproximation.polynomial Q a h F x =
      exponentialSum (representatives Q F) (representationCoefficient a h) angularFrequency x :=
  PairSpacingProjectionSum.hard_sum_eq_representative_sum Q a h F x
theorem polynomial_eq_collected (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) (F : ℕ) (x : ℝ) :
    PairFourierApproximation.polynomial Q a h F x =
      exponentialSum (frequencies Q F) (coefficient Q F a h)
        (fun ξ => 2*Real.pi*ξ) x := by
  rw [polynomial_eq_representative_sum]
  exact exponentialSum_eq_collected_scaled (representatives Q F)
    (representationCoefficient a h) frequency (2*Real.pi) x

theorem polynomial_integral_le (Q : ℕ) (a : ℕ → ℝ) (B h : ℝ) (F : ℕ)
    (hQ : 1 ≤ Q) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (t T : ℝ) (hT : 0 ≤ T) (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (∫ x in t..t+T, ‖PairFourierApproximation.polynomial Q a h F x‖ ^ 2) ≤
      B ^ 2 * h * SingletonHarmonic.harmonicSum Q ^ 3 *
        (T + 4 * (Q : ℝ) ^ 2 * kappa Q F) := by
  have hκ : 0 ≤ kappa Q F := by
    exact (PairSpacingHarmonic.H_nonneg _).trans
      (harmonic_image_le_kappa (representatives Q F) Finset.Subset.rfl)
  have he : (∫ x in t..t+T, ‖PairFourierApproximation.polynomial Q a h F x‖ ^ 2) =
      ∫ x in t..t+T, ‖exponentialSum (frequencies Q F) (coefficient Q F a h)
        (fun ξ => 2*Real.pi*ξ) x‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [polynomial_eq_collected]
  rw [he]
  apply (physical_mean_square Q F hQ (coefficient Q F a h) t T).trans
  have hb := mul_le_mul_of_nonneg_left (energy_le Q F a B h hB hh ha)
    (show 0 ≤ T + 4*(Q:ℝ)^2*kappa Q F by positivity)
  simpa only [mul_comm] using hb

end Erdos374.PairSpacingPolynomial

