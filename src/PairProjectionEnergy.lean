import PairCommonPeriod
import PairFourierBasics
import SingletonHarmonicMoving

/-! Finite Bessel energy for the actual signed divisor remainder. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PairProjectionEnergy

def remainder (Q : ℕ) (a : ℕ → ℝ) (h x : ℝ) : ℂ :=
  (SingletonResidueVariance.remainder Q a x h : ℂ)

theorem remainder_measurable (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) :
    Measurable (remainder Q a h) := by
  apply Complex.measurable_ofReal.comp
  change Measurable (fun x => SingletonMoving.remainder (Finset.Icc 1 Q) a x h)
  exact SingletonHarmonicMoving.measurable_remainder_comp _ _ _ _ measurable_id measurable_const

theorem remainder_memLp (Q : ℕ) (a : ℕ → ℝ) (h L R : ℝ) :
    MemLp (remainder Q a h) 2 (volume.restrict (Ioc L R)) := by
  apply MemLp.of_bound (remainder_measurable Q a h).aestronglyMeasurable
    (∑ n ∈ Finset.Icc 1 Q, |a n|)
  apply Filter.Eventually.of_forall
  intro x
  simp only [remainder, Complex.norm_real, Real.norm_eq_abs]
  exact SingletonHarmonicMoving.abs_remainder_le (Finset.Icc 1 Q) a x h

theorem norm_square (Q : ℕ) (a : ℕ → ℝ) (h x : ℝ) :
    ‖remainder Q a h x‖^2 = SingletonResidueVariance.remainder Q a x h ^ 2 := by
  simp only [remainder, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem finite_bessel {P : ℝ} (hP : 0 < P) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 P))) (S : Finset ℤ) :
    (∑ k ∈ S, ‖fourierCoeffOn hP f k‖^2) ≤ P⁻¹ * (∫ x in 0..P, ‖f x‖^2) := by
  have hs := hasSum_sq_fourierCoeffOn hP hf
  have hb := hs.summable.sum_le_tsum S (fun k _ => sq_nonneg ‖fourierCoeffOn hP f k‖)
  simpa only [hs.tsum_eq, sub_zero, smul_eq_mul] using hb

/-- Every finite collection of genuine common-period Fourier coefficients
has energy bounded by the exact signed-remainder mean. -/
theorem energy_le (Q : ℕ) (a : ℕ → ℝ) (B h : ℝ)
    (hB : 0 ≤ B) (hh : 0 ≤ h)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) (S : Finset ℤ) :
    (∑ k ∈ S, ‖fourierCoeffOn
      (show 0 < (PairCommonPeriod.period Q : ℝ) from by exact_mod_cast PairCommonPeriod.period_pos Q)
      (remainder Q a h) k‖^2) ≤ B^2 * h * SingletonHarmonic.harmonicSum Q ^ 3 := by
  have hP : 0 < (PairCommonPeriod.period Q : ℝ) := by
    exact_mod_cast PairCommonPeriod.period_pos Q
  apply (finite_bessel hP (remainder Q a h) (remainder_memLp Q a h 0 _) S).trans
  simp_rw [norm_square]
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hP).mpr
  simpa only [mul_comm] using PairCommonPeriod.integral_square_le Q a B h hB hh ha

end PairProjectionEnergy
