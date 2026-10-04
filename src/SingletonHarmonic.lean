import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Elementary finite harmonic bounds for the divisor covariance argument.
These estimates use all positive indices, with no coprimality restriction. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators

namespace SingletonHarmonic

def harmonicSum (Q : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 Q, 1 / (n : ℝ)

theorem harmonicSum_nonneg (Q : ℕ) : 0 ≤ harmonicSum Q := by
  exact Finset.sum_nonneg fun n _ => by positivity

theorem one_le_harmonicSum {Q : ℕ} (hQ : 1 ≤ Q) : 1 ≤ harmonicSum Q := by
  have h := Finset.single_le_sum (f := fun n : ℕ => 1 / (n : ℝ))
    (fun n (_ : n ∈ Finset.Icc 1 Q) => by positivity)
    (Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩)
  simpa [harmonicSum] using h

theorem harmonicSum_le_one_add_log (Q : ℕ) :
    harmonicSum Q ≤ 1 + Real.log Q := by
  simpa only [harmonicSum, harmonic_eq_sum_Icc, Rat.cast_sum,
    Rat.cast_inv, Rat.cast_natCast, one_div] using harmonic_le_one_add_log Q

def gcdCoordinates (p : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)

theorem gcdCoordinates_injective : Function.Injective gcdCoordinates := by
  intro p q he
  have hg : Nat.gcd p.1 p.2 = Nat.gcd q.1 q.2 := congrArg Prod.fst he
  have ha : p.1 / Nat.gcd p.1 p.2 = q.1 / Nat.gcd q.1 q.2 :=
    congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) he
  have hb : p.2 / Nat.gcd p.1 p.2 = q.2 / Nat.gcd q.1 q.2 :=
    congrArg (fun x : ℕ × ℕ × ℕ => x.2.2) he
  apply Prod.ext
  · calc
      p.1 = (p.1 / Nat.gcd p.1 p.2) * Nat.gcd p.1 p.2 :=
        (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
      _ = (q.1 / Nat.gcd q.1 q.2) * Nat.gcd q.1 q.2 := by rw [ha, hg]
      _ = q.1 := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  · calc
      p.2 = (p.2 / Nat.gcd p.1 p.2) * Nat.gcd p.1 p.2 :=
        (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm
      _ = (q.2 / Nat.gcd q.1 q.2) * Nat.gcd q.1 q.2 := by rw [hb, hg]
      _ = q.2 := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)

theorem gcdCoordinates_mem {Q : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ (Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)) :
    gcdCoordinates p ∈ (Finset.Icc 1 Q) ×ˢ
      ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)) := by
  obtain ⟨hm, hn⟩ := Finset.mem_product.mp hp
  obtain ⟨hm1, hmQ⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hn1, hnQ⟩ := Finset.mem_Icc.mp hn
  have hm0 : 0 < p.1 := hm1
  have hn0 : 0 < p.2 := hn1
  have hg0 := Nat.gcd_pos_of_pos_left p.2 hm0
  have ha0 := Nat.div_gcd_pos_of_pos_left p.2 hm0
  have hb0 : 0 < p.2 / Nat.gcd p.1 p.2 := by
    simpa only [Nat.gcd_comm] using Nat.div_gcd_pos_of_pos_left p.1 hn0
  simp only [gcdCoordinates, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨hg0, (Nat.gcd_le_left p.2 hm0).trans hmQ⟩,
    ⟨ha0, (Nat.div_le_self _ _).trans hmQ⟩,
    ⟨hb0, (Nat.div_le_self _ _).trans hnQ⟩⟩

theorem gcd_summand_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (Nat.gcd m n : ℝ) / ((m : ℝ) * n) =
      (1 / (Nat.gcd m n : ℝ)) * (1 / ((m / Nat.gcd m n : ℕ) : ℝ)) *
        (1 / ((n / Nat.gcd m n : ℕ) : ℝ)) := by
  have hg : (Nat.gcd m n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.gcd_pos_of_pos_left n hm))
  have ha : (m / Nat.gcd m n : ℕ) ≠ 0 := Nat.ne_of_gt
    (Nat.div_gcd_pos_of_pos_left n hm)
  have hb : (n / Nat.gcd m n : ℕ) ≠ 0 := by
    simpa only [Nat.gcd_comm] using Nat.ne_of_gt (Nat.div_gcd_pos_of_pos_left m hn)
  have hma : (m : ℝ) = (m / Nat.gcd m n : ℕ) * (Nat.gcd m n : ℝ) := by
    exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_left m n)).symm
  have hnb : (n : ℝ) = (n / Nat.gcd m n : ℕ) * (Nat.gcd m n : ℝ) := by
    exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_right m n)).symm
  rw [hma, hnb]
  field_simp [hg, ha, hb]

theorem gcd_sum_le_harmonicSum_cube (Q : ℕ) :
    (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
      (Nat.gcd m n : ℝ) / ((m : ℝ) * n)) ≤ (harmonicSum Q) ^ 3 := by
  let s := Finset.Icc 1 Q
  have hle := Finset.sum_le_sum_of_injOn
    (f := fun p : ℕ × ℕ => (Nat.gcd p.1 p.2 : ℝ) / ((p.1 : ℝ) * p.2))
    (g := fun t : ℕ × ℕ × ℕ => (1 / (t.1 : ℝ)) * (1 / (t.2.1 : ℝ)) *
      (1 / (t.2.2 : ℝ)))
    (s := s ×ˢ s) (t := s ×ˢ (s ×ˢ s)) gcdCoordinates
    gcdCoordinates_injective.injOn
    (by
      intro t ht
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
      exact gcdCoordinates_mem hp)
    (by
      intro p hp
      obtain ⟨hm, hn⟩ := Finset.mem_product.mp hp
      exact le_of_eq (gcd_summand_eq (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1))
    (by intro t _ _; positivity)
  rw [Finset.sum_product] at hle
  have heq : (∑ t ∈ s ×ˢ (s ×ˢ s),
      (1 / (t.1 : ℝ)) * (1 / (t.2.1 : ℝ)) * (1 / (t.2.2 : ℝ))) =
      (harmonicSum Q) ^ 3 := by
    simp only [Finset.sum_product]
    simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    simp only [harmonicSum, s]
    ring
  exact hle.trans_eq heq

theorem gcd_sum_le_log_cube (Q : ℕ) :
    (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
      (Nat.gcd m n : ℝ) / ((m : ℝ) * n)) ≤ (1 + Real.log Q) ^ 3 := by
  exact (gcd_sum_le_harmonicSum_cube Q).trans
    (pow_le_pow_left₀ (harmonicSum_nonneg Q) (harmonicSum_le_one_add_log Q) 3)

theorem lcm_sum_le_fourth_power (Q : ℕ) :
    (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q, (Nat.lcm m n : ℝ)) ≤
      (Q : ℝ) ^ 4 := by
  have hp : ∀ m ∈ Finset.Icc 1 Q, ∀ n ∈ Finset.Icc 1 Q,
      (Nat.lcm m n : ℝ) ≤ (Q : ℝ) ^ 2 := by
    intro m hm n hn
    obtain ⟨hm1, hmQ⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hn1, hnQ⟩ := Finset.mem_Icc.mp hn
    have h := (Nat.lcm_le_mul hm1 hn1).trans (Nat.mul_le_mul hmQ hnQ)
    have h' : Nat.lcm m n ≤ Q ^ 2 := by simpa only [pow_two] using h
    exact_mod_cast h'
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q, (Q : ℝ)^2 := by
      exact Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hp m hm n hn
    _ = (Q : ℝ)^4 := by simp [Nat.card_Icc]; ring

theorem product_sum_le_fourth_power (Q : ℕ) :
    (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q, (m : ℝ) * n) ≤
      (Q : ℝ) ^ 4 := by
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q, (Q : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      have h := Nat.mul_le_mul (Finset.mem_Icc.mp hm).2 (Finset.mem_Icc.mp hn).2
      have h' : m * n ≤ Q ^ 2 := by simpa only [pow_two] using h
      exact_mod_cast h'
    _ = (Q : ℝ)^4 := by simp [Nat.card_Icc]; ring

/-- Purely finite assembly of the two covariance majorants.  The analytic
covariance estimate itself is not an assumption hidden in this statement. -/
theorem weighted_pair_bound (Q : ℕ) (a : ℕ → ℝ) (B T h : ℝ)
    (hB : 0 ≤ B) (hT : 0 ≤ T) (hh : 0 ≤ h)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
      |a m * a n| * (T * h * ((Nat.gcd m n : ℝ) / ((m : ℝ) * n)) +
        2 * (Nat.lcm m n : ℝ))) ≤
      B ^ 2 * (T * h * (harmonicSum Q) ^ 3 + 2 * (Q : ℝ) ^ 4) := by
  have hmajor : (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
      |a m * a n| * (T * h * ((Nat.gcd m n : ℝ) / ((m : ℝ) * n)) +
        2 * (Nat.lcm m n : ℝ))) ≤
      ∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
        B ^ 2 * (T * h * ((Nat.gcd m n : ℝ) / ((m : ℝ) * n)) +
          2 * (Nat.lcm m n : ℝ)) := by
    apply Finset.sum_le_sum
    intro m hm
    apply Finset.sum_le_sum
    intro n hn
    have hab : |a m * a n| ≤ B ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul (ha m hm) (ha n hn) (abs_nonneg _) hB
    exact mul_le_mul_of_nonneg_right hab (by positivity)
  have heq : (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
      B ^ 2 * (T * h * ((Nat.gcd m n : ℝ) / ((m : ℝ) * n)) +
        2 * (Nat.lcm m n : ℝ))) =
      B ^ 2 * (T * h * (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
        (Nat.gcd m n : ℝ) / ((m : ℝ) * n)) +
        2 * (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q, (Nat.lcm m n : ℝ))) := by
    simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  rw [heq] at hmajor
  apply hmajor.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
  exact add_le_add
    (mul_le_mul_of_nonneg_left (gcd_sum_le_harmonicSum_cube Q) (mul_nonneg hT hh))
    (mul_le_mul_of_nonneg_left (lcm_sum_le_fourth_power Q) (by norm_num))

/-- Variant using the product period rather than the least common period. -/
theorem weighted_product_pair_bound (Q : ℕ) (a : ℕ → ℝ) (B T h : ℝ)
    (hB : 0 ≤ B) (hT : 0 ≤ T) (hh : 0 ≤ h)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
      |a m * a n| * (T * h * ((Nat.gcd m n : ℝ) / ((m : ℝ) * n)) +
        2 * ((m : ℝ) * n))) ≤
      B ^ 2 * (T * h * (harmonicSum Q) ^ 3 + 2 * (Q : ℝ) ^ 4) := by
  have hmajor : (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
      |a m * a n| * (T * h * ((Nat.gcd m n : ℝ) / ((m : ℝ) * n)) +
        2 * ((m : ℝ) * n))) ≤
      ∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
        B ^ 2 * (T * h * ((Nat.gcd m n : ℝ) / ((m : ℝ) * n)) +
          2 * ((m : ℝ) * n)) := by
    apply Finset.sum_le_sum
    intro m hm
    apply Finset.sum_le_sum
    intro n hn
    have hab : |a m * a n| ≤ B ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul (ha m hm) (ha n hn) (abs_nonneg _) hB
    exact mul_le_mul_of_nonneg_right hab (by positivity)
  have heq : (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
      B ^ 2 * (T * h * ((Nat.gcd m n : ℝ) / ((m : ℝ) * n)) +
        2 * ((m : ℝ) * n))) =
      B ^ 2 * (T * h * (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q,
        (Nat.gcd m n : ℝ) / ((m : ℝ) * n)) +
        2 * (∑ m ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Icc 1 Q, (m : ℝ) * n)) := by
    simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  rw [heq] at hmajor
  apply hmajor.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
  exact add_le_add
    (mul_le_mul_of_nonneg_left (gcd_sum_le_harmonicSum_cube Q) (mul_nonneg hT hh))
    (mul_le_mul_of_nonneg_left (product_sum_le_fourth_power Q) (by norm_num))

end SingletonHarmonic
