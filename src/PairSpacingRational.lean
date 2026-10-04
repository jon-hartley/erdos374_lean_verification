import PairSpacingHarmonic
import Mathlib.Data.Int.Interval

noncomputable section
open scoped BigOperators

namespace Erdos374.PairSpacingRational

def modes (M : ℕ) : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0

def representatives (Q F : ℕ) : Finset (ℕ × ℤ) :=
  ((Finset.Icc 1 Q).product (modes (Q * F))).filter
    (fun p => |p.2| ≤ (p.1 * F : ℕ))

def frequency (p : ℕ × ℤ) : ℝ := (p.2 : ℝ) / (p.1 : ℝ)

def frequencies (Q F : ℕ) : Finset ℝ := (representatives Q F).image frequency

theorem modes_card (M : ℕ) : (modes M).card = 2 * M := by
  have hzero : (0 : ℤ) ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) := by simp
  rw [modes, Finset.card_erase_of_mem hzero, Int.card_Icc]
  have h : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
  rw [h]
  omega

theorem representatives_card_le (Q F : ℕ) : (representatives Q F).card ≤ 2 * F * Q ^ 2 := by
  calc
    _ ≤ ((Finset.Icc 1 Q).product (modes (Q * F))).card := Finset.card_filter_le ..
    _ = Q * (2 * (Q * F)) := by
      rw [Finset.product_eq_sprod, Finset.card_product, modes_card]
      simp
    _ = _ := by ring

theorem frequencies_card_le (Q F : ℕ) : (frequencies Q F).card ≤ 2 * F * Q ^ 2 :=
  (Finset.card_image_le).trans (representatives_card_le Q F)

theorem mem_representatives {Q F : ℕ} {p : ℕ × ℤ}
    (hp : p ∈ representatives Q F) :
    1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 ≠ 0 ∧ |p.2| ≤ (p.1 * F : ℕ) := by
  rcases Finset.mem_filter.mp hp with ⟨hprod, habs⟩
  rcases Finset.mem_product.mp hprod with ⟨hn, hk⟩
  exact ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2,
    (Finset.mem_erase.mp hk).1, habs⟩

theorem mem_representatives_iff {Q F : ℕ} {p : ℕ × ℤ} :
    p ∈ representatives Q F ↔
      1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 ≠ 0 ∧ |p.2| ≤ (p.1 * F : ℕ) := by
  refine ⟨mem_representatives, ?_⟩
  rintro ⟨hn, hQ, hk, habs⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hn, hQ⟩, ?_⟩, habs⟩
  apply Finset.mem_erase.mpr
  refine ⟨hk, Finset.mem_Icc.mpr ?_⟩
  have hm : (p.1 * F : ℤ) ≤ (Q * F : ℕ) := by exact_mod_cast Nat.mul_le_mul_right F hQ
  have habs' : |p.2| ≤ (Q * F : ℕ) := habs.trans hm
  exact abs_le.mp habs'

theorem rational_separation {Q m n : ℕ} {k l : ℤ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmQ : m ≤ Q) (hnQ : n ≤ Q)
    (hne : (k : ℝ) / (m : ℝ) ≠ (l : ℝ) / (n : ℝ)) :
    1 / (Q : ℝ) ^ 2 ≤ |(k : ℝ) / (m : ℝ) - (l : ℝ) / (n : ℝ)| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ0 : (0 : ℝ) < Q := hm0.trans_le (by exact_mod_cast hmQ)
  have hnum : k * (n : ℤ) - l * (m : ℤ) ≠ 0 := by
    intro hh
    apply hne
    apply (div_eq_div_iff hm0.ne' hn0.ne').mpr
    exact_mod_cast sub_eq_zero.mp hh
  have hnum1 : (1 : ℤ) ≤ |k * (n : ℤ) - l * (m : ℤ)| := by
    have := abs_pos.mpr hnum
    omega
  have hnumR : (1 : ℝ) ≤ |(k : ℝ) * (n : ℝ) - (l : ℝ) * (m : ℝ)| := by
    exact_mod_cast hnum1
  have hden : (m : ℝ) * (n : ℝ) ≤ (Q : ℝ) ^ 2 := by
    rw [pow_two]
    exact mul_le_mul (by exact_mod_cast hmQ) (by exact_mod_cast hnQ) hn0.le hQ0.le
  calc
    _ ≤ 1 / ((m : ℝ) * (n : ℝ)) := one_div_le_one_div_of_le (mul_pos hm0 hn0) hden
    _ ≤ |(k : ℝ) * (n : ℝ) - (l : ℝ) * (m : ℝ)| / ((m : ℝ) * (n : ℝ)) :=
      div_le_div_of_nonneg_right hnumR (mul_nonneg hm0.le hn0.le)
    _ = _ := by
      rw [div_sub_div _ _ hm0.ne' hn0.ne', abs_div,
        abs_of_pos (mul_pos hm0 hn0)]
      congr 2
      ring

theorem frequencies_separated (Q F : ℕ) :
    ∀ x ∈ frequencies Q F, ∀ y ∈ frequencies Q F, x ≠ y →
      1 / (Q : ℝ) ^ 2 ≤ |x - y| := by
  intro x hx y hy hne
  rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
  have hp' := mem_representatives hp
  have hq' := mem_representatives hq
  exact rational_separation hp'.1 hq'.1 hp'.2.1 hq'.2.1 hne

end Erdos374.PairSpacingRational
