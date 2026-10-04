import SingletonDivisor

/-! A pointwise signed width-freezing inequality. The original weights keep
their signs; absolute coefficients occur only in the auxiliary error term. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SingletonMoving
open SingletonDivisor

def count (n : ℕ) (x h : ℝ) : ℝ := (⌊x/n⌋:ℝ)-(⌊(x-h)/n⌋:ℝ)

def remainder (S : Finset ℕ) (a : ℕ → ℝ) (x h : ℝ) : ℝ :=
  ∑n∈S, a n * discrepancy n x h

def mass (S : Finset ℕ) (a : ℕ → ℝ) : ℝ := ∑n∈S, a n/(n:ℝ)

theorem count_mono (n : ℕ) (x h k : ℝ) (hh : h≤k) :
    count n x h ≤ count n x k := by
  have hh' : (x-k)/(n:ℝ)≤(x-h)/(n:ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  have hi : (⌊(x-k)/(n:ℝ)⌋:ℝ)≤(⌊(x-h)/(n:ℝ)⌋:ℝ) := by
    exact_mod_cast Int.floor_mono hh'
  unfold count
  linarith

theorem count_nonneg (n : ℕ) (x h : ℝ) (hh : 0≤h) : 0≤count n x h := by
  have ht := count_mono n x 0 h hh
  simpa [count] using ht

theorem discrepancy_change (n : ℕ) (x h k : ℝ) :
    discrepancy n x h - discrepancy n x k = count n (x-k) (h-k) - (h-k)/n := by
  unfold discrepancy count
  rw [show x-k-(h-k)=x-h by ring, sub_div]
  ring

theorem abs_change_le (n : ℕ) (x h k E : ℝ) (hk : k≤h) (hE : h-k≤E) :
    |discrepancy n x h - discrepancy n x k| ≤ count n (x-k) E + E/n := by
  rw [discrepancy_change]
  calc
    _ ≤ |count n (x-k) (h-k)| + |(h-k)/(n:ℝ)| := abs_sub _ _
    _ = count n (x-k) (h-k) + (h-k)/(n:ℝ) := by
      rw [abs_of_nonneg (count_nonneg n _ _ (sub_nonneg.mpr hk)),
        abs_of_nonneg (div_nonneg (sub_nonneg.mpr hk) (Nat.cast_nonneg n))]
    _ ≤ _ := add_le_add (count_mono n (x-k) (h-k) E hE)
      (div_le_div_of_nonneg_right hE (Nat.cast_nonneg n))

theorem weighted_count (S : Finset ℕ) (a : ℕ → ℝ) (x h : ℝ) :
    (∑n∈S, a n*count n x h) = remainder S a x h + h*mass S a := by
  unfold remainder mass count discrepancy
  rw [Finset.mul_sum, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem freeze (S : Finset ℕ) (a : ℕ → ℝ) (x h k E : ℝ)
    (hk : k≤h) (hE : h-k≤E) :
    |remainder S a x h - remainder S a x k| ≤
      |remainder S (fun n => |a n|) (x-k) E| + 2*E*mass S (fun n => |a n|) := by
  have heq : remainder S a x h - remainder S a x k =
      ∑n∈S, a n*(discrepancy n x h-discrepancy n x k) := by
    simp only [remainder, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑n∈S, |a n*(discrepancy n x h-discrepancy n x k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑n∈S, |a n| *(count n (x-k) E + E/n) := by
      apply Finset.sum_le_sum
      intro n _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_change_le n x h k E hk hE) (abs_nonneg _)
    _ = remainder S (fun n => |a n|) (x-k) E + 2*E*mass S (fun n => |a n|) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, weighted_count]
      have hm : (∑n∈S, |a n| *(E/n)) = E*mass S (fun n => |a n|) := by
        rw [mass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      rw [hm]
      ring
    _ ≤ _ := add_le_add (le_abs_self (remainder S (fun n => |a n|) (x-k) E)) le_rfl

end SingletonMoving

