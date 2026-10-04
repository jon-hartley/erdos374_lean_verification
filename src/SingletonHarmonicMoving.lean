import SingletonMoving
import SingletonHarmonic
import SingletonHarmonicPartition

/-! Integrating the signed width-freezing inequality.  All integrability
claims are proved for measurable changes of the location and width. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SingletonHarmonicMoving
open SingletonMoving

theorem abs_remainder_le (S : Finset ℕ) (a : ℕ → ℝ) (x h : ℝ) :
    |remainder S a x h| ≤ ∑ n ∈ S, |a n| := by
  unfold remainder
  calc
    _ ≤ ∑ n ∈ S, |a n * SingletonDivisor.discrepancy n x h| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n _
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (SingletonDivisor.abs_discrepancy_le_one n x h) (abs_nonneg (a n))

theorem measurable_remainder_comp (S : Finset ℕ) (a : ℕ → ℝ) (g h : ℝ → ℝ)
    (hg : Measurable g) (hh : Measurable h) :
    Measurable (fun x => remainder S a (g x) (h x)) := by
  unfold remainder
  apply Finset.measurable_sum
  intro n _
  unfold SingletonDivisor.discrepancy
  fun_prop

theorem square_intervalIntegrable_comp (S : Finset ℕ) (a : ℕ → ℝ) (g h : ℝ → ℝ)
    (hg : Measurable g) (hh : Measurable h) (L R : ℝ) :
    IntervalIntegrable (fun x => remainder S a (g x) (h x) ^ 2) volume L R := by
  have hmeas : Measurable (fun x => remainder S a (g x) (h x) ^ 2) :=
    (measurable_remainder_comp S a g h hg hh).pow_const 2
  have hi : IntegrableOn (fun x => remainder S a (g x) (h x) ^ 2) (Set.uIcc L R) := by
    apply Measure.integrableOn_of_bounded isCompact_uIcc.measure_lt_top.ne
      hmeas.aestronglyMeasurable (M := (∑ n ∈ S, |a n|) ^ 2)
    apply Filter.Eventually.of_forall
    intro x
    have hb := pow_le_pow_left₀ (abs_nonneg (remainder S a (g x) (h x)))
      (abs_remainder_le S a (g x) (h x)) 2
    simpa only [Real.norm_eq_abs, abs_pow] using hb
  exact hi.intervalIntegrable

theorem mass_abs_nonneg (S : Finset ℕ) (a : ℕ → ℝ) :
    0 ≤ mass S (fun n => |a n|) := by
  unfold mass
  exact Finset.sum_nonneg fun n _ => by positivity

theorem mass_abs_le (Q : ℕ) (a : ℕ → ℝ) (B : ℝ)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    mass (Finset.Icc 1 Q) (fun n => |a n|) ≤ B * SingletonHarmonic.harmonicSum Q := by
  unfold mass SingletonHarmonic.harmonicSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  simpa only [mul_one_div] using div_le_div_of_nonneg_right (ha n hn) (Nat.cast_nonneg n)

theorem square_freeze_le (S : Finset ℕ) (a : ℕ → ℝ) (x h k E : ℝ)
    (hk : k ≤ h) (hE : h - k ≤ E) (hE0 : 0 ≤ E) :
    remainder S a x h ^ 2 ≤ 3 *
      (remainder S a x k ^ 2 + remainder S (fun n => |a n|) (x - k) E ^ 2 +
        (2 * E * mass S (fun n => |a n|)) ^ 2) := by
  have hz : 0 ≤ 2 * E * mass S (fun n => |a n|) :=
    mul_nonneg (mul_nonneg (by norm_num) hE0) (mass_abs_nonneg S a)
  have hab : |remainder S a x h| ≤ |remainder S a x k| +
      |remainder S (fun n => |a n|) (x - k) E| +
        2 * E * mass S (fun n => |a n|) := by
    have htri := abs_add_le (remainder S a x h - remainder S a x k) (remainder S a x k)
    have hfreeze := freeze S a x h k E hk hE
    rw [sub_add_cancel] at htri
    linarith
  have hp := pow_le_pow_left₀ (abs_nonneg (remainder S a x h)) hab 2
  have hv := sq_nonneg (|remainder S a x k| -
    |remainder S (fun n => |a n|) (x - k) E|)
  have hw := sq_nonneg (|remainder S a x k| - 2 * E * mass S (fun n => |a n|))
  have hu := sq_nonneg (|remainder S (fun n => |a n|) (x - k) E| -
    2 * E * mass S (fun n => |a n|))
  simp only [sq_abs] at hp hv hw hu
  nlinarith [sq_abs (remainder S a x k),
    sq_abs (remainder S (fun n => |a n|) (x - k) E)]

theorem integral_square_freeze_le (S : Finset ℕ) (a : ℕ → ℝ) (h : ℝ → ℝ)
    (hh : Measurable h) (k E t T : ℝ) (hT : 0 ≤ T) (hE0 : 0 ≤ E)
    (hk : ∀ x ∈ Set.Icc t (t + T), k ≤ h x)
    (hE : ∀ x ∈ Set.Icc t (t + T), h x - k ≤ E) :
    (∫ x in t..t + T, remainder S a x (h x) ^ 2) ≤ 3 *
      ((∫ x in t..t + T, remainder S a x k ^ 2) +
        (∫ x in t..t + T, remainder S (fun n => |a n|) (x - k) E ^ 2) +
          T * (2 * E * mass S (fun n => |a n|)) ^ 2) := by
  have hi := square_intervalIntegrable_comp S a id h measurable_id hh t (t + T)
  have hf := square_intervalIntegrable_comp S a id (fun _ => k)
    measurable_id measurable_const t (t + T)
  have hb := square_intervalIntegrable_comp S (fun n => |a n|) (fun x => x - k)
    (fun _ => E) (measurable_id.sub measurable_const) measurable_const t (t + T)
  have hc : IntervalIntegrable (fun _ : ℝ => (2 * E * mass S (fun n => |a n|)) ^ 2)
      volume t (t + T) := intervalIntegrable_const
  have hmajor := intervalIntegral.integral_mono_on (le_add_of_nonneg_right hT)
    hi (((hf.add hb).add hc).const_mul 3)
    (fun x hx => square_freeze_le S a x (h x) k E (hk x hx) (hE x hx) hE0)
  simp only [id_eq] at hi hf hmajor
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hf.add hb) hc,
    intervalIntegral.integral_add hf hb, intervalIntegral.integral_const] at hmajor
  simpa only [add_sub_cancel_left, smul_eq_mul] using hmajor

end SingletonHarmonicMoving
