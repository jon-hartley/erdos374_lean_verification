import SingletonResidueVariance
import Mathlib.Data.Nat.Factorial.Basic

/-! Exact mean-square control over a common period. The bounded boundary
error disappears by repeating the period an arbitrary number of times. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set intervalIntegral

namespace PairCommonPeriod

theorem le_of_nat_mul_le (I A C : ℝ)
    (h : ∀ k : ℕ, (k : ℝ) * I ≤ (k : ℝ) * A + C) : I ≤ A := by
  by_contra hn
  have hd : 0 < I - A := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨k, hk⟩ := exists_nat_gt (C / (I - A))
  have hk' : C < (k : ℝ) * (I - A) := (div_lt_iff₀ hd).mp hk
  nlinarith [h k]

theorem periodic_mean_le (f : ℝ → ℝ) (P A C : ℝ) (hP : 0 < P)
    (hp : Function.Periodic f P)
    (hi : ∀ a b, IntervalIntegrable f volume a b)
    (hb : ∀ T : ℝ, 0 ≤ T → (∫ x in 0..T, f x) ≤ T * A + C) :
    (∫ x in 0..P, f x) ≤ P * A := by
  apply le_of_nat_mul_le _ _ C
  intro k
  have hk := hp.intervalIntegral_add_zsmul_eq (k : ℤ) 0 hi
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast] at hk
  have h := hb ((k : ℝ) * P) (mul_nonneg (Nat.cast_nonneg k) hP.le)
  rw [hk] at h
  simpa only [mul_assoc] using h

/-- A nonnegative periodic integrand needs at most one extra full period
to cover any real interval of nonnegative length. -/
theorem integral_le_cover (f : ℝ → ℝ) (P : ℝ) (hP : 0 < P)
    (hp : Function.Periodic f P)
    (hi : ∀ a b, IntervalIntegrable f volume a b)
    (hn : ∀ x, 0 ≤ f x) (t T : ℝ) (_hT : 0 ≤ T) :
    (∫ x in t..t+T, f x) ≤ (T/P+1) * (∫ x in 0..P, f x) := by
  let e := Int.fract (T/P)*P
  let q := ⌊T/P⌋
  have he : 0 ≤ e ∧ e < P := by
    constructor
    · exact mul_nonneg (Int.fract_nonneg _) hP.le
    · simpa [e] using mul_lt_mul_of_pos_right (Int.fract_lt_one (T/P)) hP
  have hsplit : e+(q:ℝ)*P=T := by
    simpa only [zsmul_eq_mul] using Int.fract_div_mul_self_add_zsmul_eq P T hP.ne'
  have hpI : (∫x in t+e..t+e+(q:ℝ)*P, f x) =
      (q:ℝ)*(∫x in 0..P, f x) := by
    simpa only [zsmul_eq_mul, zero_add, hp.intervalIntegral_add_eq (t+e) 0] using
      hp.intervalIntegral_add_zsmul_eq q (t+e) hi
  have hadd : (∫x in t..t+T, f x) =
      (∫x in t..t+e, f x) + (q:ℝ)*(∫x in 0..P, f x) := by
    rw [← hpI, integral_add_adjacent_intervals (hi _ _) (hi _ _)]
    congr 1
    linarith [hsplit]
  have hsmall : (∫x in t..t+e, f x) ≤ (∫x in 0..P, f x) := by
    have h := integral_mono_interval (f := f) le_rfl (by linarith : t ≤ t+e)
      (by linarith : t+e ≤ t+P) (Filter.Eventually.of_forall hn) (hi t (t+P))
    simpa only [hp.intervalIntegral_add_eq t 0, zero_add] using h
  have hfull : 0 ≤ (∫x in 0..P, f x) := integral_nonneg_of_forall hP.le hn
  have hq : (q : ℝ) ≤ T/P := Int.floor_le _
  rw [hadd]
  nlinarith [mul_le_mul_of_nonneg_right hq hfull]

def period (Q : ℕ) : ℕ := Q.factorial

theorem period_pos (Q : ℕ) : 0 < period Q := Nat.factorial_pos Q

theorem dvd_period {Q n : ℕ} (hn : n ∈ Finset.Icc 1 Q) : n ∣ period Q :=
  Nat.dvd_factorial (by have := (Finset.mem_Icc.mp hn).1; omega)
    (Finset.mem_Icc.mp hn).2

theorem discrepancy_periodic {Q n : ℕ} (hn : n ∈ Finset.Icc 1 Q) (h : ℝ) :
    Function.Periodic (fun x => SingletonDivisor.discrepancy n x h) (period Q : ℝ) := by
  obtain ⟨k, hk⟩ := dvd_period hn
  have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  have hp := (SingletonDivisor.periodic n hn0 h).nsmul k
  simpa only [nsmul_eq_mul, hk, Nat.cast_mul, mul_comm] using hp

theorem remainder_periodic (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) :
    Function.Periodic (fun x => SingletonResidueVariance.remainder Q a x h)
      (period Q : ℝ) := by
  intro x
  unfold SingletonResidueVariance.remainder
  apply Finset.sum_congr rfl
  intro n hn
  exact congrArg (fun y => a n * y) (discrepancy_periodic hn h x)

theorem square_periodic (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) :
    Function.Periodic (fun x => SingletonResidueVariance.remainder Q a x h ^ 2)
      (period Q : ℝ) := by
  intro x
  exact congrArg (fun y => y^2) (remainder_periodic Q a h x)

/-- The exact common-period mean has no boundary error. This is deduced
from the checked CRT covariance bound by arbitrary periodic repetition. -/
theorem integral_square_le (Q : ℕ) (a : ℕ → ℝ) (B h : ℝ)
    (hB : 0 ≤ B) (hh : 0 ≤ h)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (∫ x in 0..(period Q : ℝ), SingletonResidueVariance.remainder Q a x h ^ 2) ≤
      (period Q : ℝ) * (B^2 * h * SingletonHarmonic.harmonicSum Q ^ 3) := by
  apply periodic_mean_le _ _ _ (2*B^2*(Q:ℝ)^4)
    (by exact_mod_cast period_pos Q) (square_periodic Q a h)
    (SingletonResidueVariance.square_intervalIntegrable Q a h)
  intro T hT
  have h := SingletonResidueVariance.integral_square_le Q a B h 0 T hB hh hT ha
  simp only [zero_add] at h
  convert h using 1
  ring

end PairCommonPeriod
