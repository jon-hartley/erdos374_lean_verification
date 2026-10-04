import Mathlib.Algebra.Order.Floor.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Finite residue identities for the covariance of divisor-window counts. -/

open scoped BigOperators

namespace SingletonResidue

/-- The integer count on a unit cell, with arbitrary integral width. -/
def count (a : ℕ) (K : ℤ) (q : ℕ) : ℤ :=
  (q : ℤ) / (a : ℤ) - ((q : ℤ) - K) / (a : ℤ)

theorem sum_count {a : ℕ} (ha : 0 < a) (K : ℤ) :
    ∑ q ∈ Finset.range a, count a K q = K := by
  unfold count
  rw [Finset.sum_sub_distrib]
  have hzero := Int.sum_range_add_ediv 0 ha
  have hneg := Int.sum_range_add_ediv (-K) ha
  simp only [zero_add] at hzero
  have hsub : (∑ q ∈ Finset.range a, ((q : ℤ) - K) / (a : ℤ)) = -K := by
    simpa only [sub_eq_add_neg, add_comm] using hneg
  rw [hzero, hsub]
  omega

theorem count_mod {a : ℕ} (ha : 0 < a) (K : ℤ) (q : ℕ) :
    count a K q = count a K (q % a) := by
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  have hq : (q : ℤ) = (q / a : ℕ) * (a : ℤ) + (q % a : ℕ) := by
    have hqn : q = q / a * a + q % a := by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod q a).symm
    exact_mod_cast hqn
  unfold count
  conv_lhs => rw [hq]
  rw [show (q / a : ℕ) * (a : ℤ) + (q % a : ℕ) - K =
    (q / a : ℕ) * (a : ℤ) + ((q % a : ℕ) - K) by ring]
  rw [Int.mul_add_ediv_right _ _ ha0, Int.mul_add_ediv_right _ _ ha0]
  omega

/-- Chinese remainder independence, expressed directly with finite natural ranges. -/
theorem sum_range_crt {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (f g : ℕ → ℝ) :
    (∑ q ∈ Finset.range (a * b), f (q % a) * g (q % b)) =
      (∑ i ∈ Finset.range a, f i) * (∑ j ∈ Finset.range b, g j) := by
  have hprod : (∑ p ∈ Finset.range a ×ˢ Finset.range b, f p.1 * g p.2) =
      (∑ i ∈ Finset.range a, f i) * (∑ j ∈ Finset.range b, g j) := by
    rw [Finset.sum_product, Finset.sum_mul_sum]
  rw [← hprod]
  refine Finset.sum_bij (fun q _ => (q % a, q % b)) ?_ ?_ ?_ ?_
  · intro q hq
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ ha),
      Finset.mem_range.mpr (Nat.mod_lt _ hb)⟩
  · intro q hq r hr hqr
    have hqa : q ≡ r [MOD a] := congrArg Prod.fst hqr
    have hqb : q ≡ r [MOD b] := congrArg Prod.snd hqr
    have hmod : q ≡ r [MOD a * b] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨hqa, hqb⟩
    exact hmod.eq_of_lt_of_lt (Finset.mem_range.mp hq) (Finset.mem_range.mp hr)
  · intro p hp
    have hp' := Finset.mem_product.mp hp
    let q := Nat.chineseRemainder hab p.1 p.2
    refine ⟨q, Finset.mem_range.mpr
      (Nat.chineseRemainder_lt_mul hab _ _ (ne_of_gt ha) (ne_of_gt hb)), ?_⟩
    apply Prod.ext
    · calc
        (q : ℕ) % a = p.1 % a := q.prop.1
        _ = p.1 := Nat.mod_eq_of_lt (Finset.mem_range.mp hp'.1)
    · calc
        (q : ℕ) % b = p.2 % b := q.prop.2
        _ = p.2 := Nat.mod_eq_of_lt (Finset.mem_range.mp hp'.2)
  · intro q hq
    rfl

theorem sum_count_real {a : ℕ} (ha : 0 < a) (K : ℤ) :
    ∑ q ∈ Finset.range a, (count a K q : ℝ) = (K : ℝ) := by
  exact_mod_cast sum_count ha K

/-- The complete residue sum of a centered count. -/
theorem sum_centered {a : ℕ} (ha : 0 < a) (K : ℤ) (h : ℝ) :
    ∑ q ∈ Finset.range a, ((count a K q : ℝ) - h / a) = (K : ℝ) - h := by
  rw [Finset.sum_sub_distrib, sum_count_real ha]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  field_simp

/-- Exact finite centered covariance for a coprime pair. No analytic premise is used. -/
theorem sum_centered_product {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (K : ℤ) (h : ℝ) :
    (∑ q ∈ Finset.range (a * b),
      ((count a K q : ℝ) - h / a) * ((count b K q : ℝ) - h / b)) =
        ((K : ℝ) - h) ^ 2 := by
  calc
    _ = ∑ q ∈ Finset.range (a * b),
        ((count a K (q % a) : ℝ) - h / a) *
          ((count b K (q % b) : ℝ) - h / b) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [count_mod ha K q, count_mod hb K q]
    _ = (∑ i ∈ Finset.range a, ((count a K i : ℝ) - h / a)) *
        (∑ j ∈ Finset.range b, ((count b K j : ℝ) - h / b)) :=
      sum_range_crt ha hb hab (fun i => (count a K i : ℝ) - h / a)
        (fun j => (count b K j : ℝ) - h / b)
    _ = ((K : ℝ) - h) ^ 2 := by rw [sum_centered ha, sum_centered hb]; ring

end SingletonResidue
