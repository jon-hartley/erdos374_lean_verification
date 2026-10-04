import PairCommonPeriod
import PairSpacingRational

/-! Sparse integer modes on the factorial common period. Every compatible
representation of a retained physical frequency is retained. -/
set_option autoImplicit false
noncomputable section

namespace PairCommonModes
open PairCommonPeriod Erdos374.PairSpacingRational

def multiplier (Q n : ℕ) : ℕ := period Q / n

theorem multiplier_mul {Q n : ℕ} (hn : n ∈ Finset.Icc 1 Q) :
    multiplier Q n * n = period Q := Nat.div_mul_cancel (dvd_period hn)

theorem multiplier_pos {Q n : ℕ} (hn : n ∈ Finset.Icc 1 Q) :
    0 < multiplier Q n := by
  apply Nat.div_pos (Nat.le_of_dvd (period_pos Q) (dvd_period hn))
  have := (Finset.mem_Icc.mp hn).1
  omega

def commonMode (Q : ℕ) (p : ℕ × ℤ) : ℤ := (multiplier Q p.1 : ℤ) * p.2

def modes (Q F : ℕ) : Finset ℤ := (representatives Q F).image (commonMode Q)

theorem commonMode_frequency {Q : ℕ} (p : ℕ × ℤ)
    (hn : p.1 ∈ Finset.Icc 1 Q) :
    (commonMode Q p : ℝ) = (period Q : ℝ) * frequency p := by
  have hn0 : (p.1 : ℝ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (show p.1 ≠ 0 by omega)
  have hm : (multiplier Q p.1 : ℝ) * p.1 = period Q := by
    exact_mod_cast multiplier_mul hn
  simp only [commonMode, frequency, Int.cast_mul, Int.cast_natCast]
  rw [← mul_div_assoc]
  apply (eq_div_iff hn0).mpr
  rw [← hm]
  ring

theorem commonMode_ne_zero {Q F : ℕ} {p : ℕ × ℤ}
    (hp : p ∈ representatives Q F) : commonMode Q p ≠ 0 := by
  have hp' := mem_representatives hp
  apply mul_ne_zero
  · exact_mod_cast (multiplier_pos (Finset.mem_Icc.mpr ⟨hp'.1,hp'.2.1⟩)).ne'
  · exact hp'.2.2.1

theorem abs_commonMode_le {Q F : ℕ} {p : ℕ × ℤ}
    (hp : p ∈ representatives Q F) :
    |commonMode Q p| ≤ (period Q * F : ℕ) := by
  have hp' := mem_representatives hp
  have hn := Finset.mem_Icc.mpr ⟨hp'.1,hp'.2.1⟩
  simp only [commonMode, abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
  calc
    _ ≤ (multiplier Q p.1 : ℤ) * (p.1 * F : ℕ) :=
      mul_le_mul_of_nonneg_left hp'.2.2.2 (Int.natCast_nonneg _)
    _ = (period Q * F : ℕ) := by
      rw [Nat.cast_mul, ← mul_assoc, ← Nat.cast_mul, multiplier_mul hn, Nat.cast_mul]

theorem compatible_mem_representatives {Q F n : ℕ} {K k : ℤ}
    (hK : K ∈ modes Q F) (hn : n ∈ Finset.Icc 1 Q)
    (he : (multiplier Q n : ℤ) * k = K) : (n,k) ∈ representatives Q F := by
  obtain ⟨p,hp,hpK⟩ := Finset.mem_image.mp hK
  have hK0 : K ≠ 0 := hpK ▸ commonMode_ne_zero hp
  have hKb : |K| ≤ (period Q * F : ℕ) := hpK ▸ abs_commonMode_le hp
  have hk0 : k ≠ 0 := by intro hk; apply hK0; rw [← he,hk,mul_zero]
  apply mem_representatives_iff.mpr
  refine ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2,hk0,?_⟩
  have hmp : (0:ℤ) < multiplier Q n := by exact_mod_cast multiplier_pos hn
  apply (mul_le_mul_iff_right₀ hmp).mp
  rw [← abs_of_nonneg hmp.le, ← abs_mul, he]
  have hem : (multiplier Q n : ℤ) * (n * F : ℕ) = (period Q * F : ℕ) := by
    rw [Nat.cast_mul, ← mul_assoc, ← Nat.cast_mul, multiplier_mul hn, Nat.cast_mul]
  simpa only [abs_of_nonneg hmp.le, hem] using hKb

theorem modes_card_le (Q F : ℕ) : (modes Q F).card ≤ 2 * F * Q^2 :=
  Finset.card_image_le.trans (representatives_card_le Q F)

theorem same_commonMode_iff {Q : ℕ} (p q : ℕ × ℤ)
    (hp : p.1 ∈ Finset.Icc 1 Q) (hq : q.1 ∈ Finset.Icc 1 Q) :
    commonMode Q p = commonMode Q q ↔ frequency p = frequency q := by
  have hP : (period Q : ℝ) ≠ 0 := by exact_mod_cast (period_pos Q).ne'
  rw [← Int.cast_inj (α := ℝ), commonMode_frequency p hp, commonMode_frequency q hq]
  constructor
  · exact mul_left_cancel₀ hP
  · intro h
    rw [h]

end PairCommonModes
