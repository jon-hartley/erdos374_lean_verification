import E374.D5Exclusion
import E374.Mertens

/-!
# Positive lower density of `T5` (Chebyshev only, no PNT)

`T5 = {m : m squarefree, 2 ∣ m, P⁺(m) > m^{99/100}}`. We count `m = r P` with `r` even
squarefree, `r ≤ X^{1/100}/8`, and `P` a prime in `(⌊X/r⌋/4, ⌊X/r⌋]`.
* Even squarefree numbers: `#{r ≤ t} ≥ t/24 - 2` (odd squarefree `s ≤ y`: `≥ y/12 - 1`).
* Abel summation: `∑_{r ∈ B, r ≤ R} 1/r ≥ c log R - C`.
* Chebyshev (Mathlib): `θ(y) - θ(y/4) ≥ (y/4) log 2` for large `y`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option maxHeartbeats 3200000

noncomputable section
open scoped BigOperators
open Finset

namespace Erdos374.D35

/-! ## Squarefree counting -/

theorem sum_inv_sq_sub_one_eq (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Finset.Icc 3 N, (1 : ℝ) / ((n : ℝ) ^ 2 - 1) =
      5 / 12 - 1 / (2 * (N : ℝ)) - 1 / (2 * ((N : ℝ) + 1)) := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by norm_num)]
    norm_num
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have e : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [e]
    have h1 : ((N : ℝ) + 1) ^ 2 - 1 ≠ 0 := by nlinarith
    have h2 : (N : ℝ) ≠ 0 := by linarith
    have h3 : (N : ℝ) + 1 ≠ 0 := by linarith
    have h4 : (N : ℝ) + 1 + 1 ≠ 0 := by linarith
    field_simp
    ring

theorem sum_inv_sq_sub_one_le (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Finset.Icc 3 N, (1 : ℝ) / ((n : ℝ) ^ 2 - 1) ≤ 5 / 12 := by
  rw [sum_inv_sq_sub_one_eq N hN]
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have : (0 : ℝ) ≤ 1 / (2 * (N : ℝ)) := by positivity
  have : (0 : ℝ) ≤ 1 / (2 * ((N : ℝ) + 1)) := by positivity
  linarith

/-- Odd squarefree numbers up to `y`: at least `y/12 - 1`. -/
theorem card_odd_squarefree_ge (y : ℕ) :
    (y : ℝ) / 12 - 1 ≤
      (((Finset.Icc 1 y).filter (fun s => ¬ 2 ∣ s ∧ Squarefree s)).card : ℝ) := by
  classical
  set Odd' := (Finset.Icc 1 y).filter (fun s => ¬ 2 ∣ s)
  set Bad := (Finset.Icc 3 y).biUnion (fun n => (Finset.Icc 1 y).filter (fun s => n ^ 2 ∣ s))
  have hsub : Odd' ⊆ ((Finset.Icc 1 y).filter (fun s => ¬ 2 ∣ s ∧ Squarefree s)) ∪ Bad := by
    intro s hs
    rw [Finset.mem_filter] at hs
    by_cases hsq : Squarefree s
    · apply Finset.mem_union_left; rw [Finset.mem_filter]; exact ⟨hs.1, hs.2, hsq⟩
    · apply Finset.mem_union_right
      rw [Nat.squarefree_iff_prime_squarefree] at hsq
      push_neg at hsq
      obtain ⟨p, hp, hpp⟩ := hsq
      have hp2 : p ≠ 2 := by
        rintro rfl; exact hs.2 (dvd_trans (dvd_mul_left 2 2) hpp)
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs.1).1
      have hpy : p ≤ y := by
        have := Nat.le_of_dvd (by omega) hpp
        have : p ≤ p * p := Nat.le_mul_self p
        have := (Finset.mem_Icc.mp hs.1).2
        omega
      rw [Finset.mem_biUnion]
      exact ⟨p, Finset.mem_Icc.mpr ⟨hp3, hpy⟩, Finset.mem_filter.mpr ⟨hs.1, by rwa [pow_two]⟩⟩
  have hc1 := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hBad : (Bad.card : ℝ) ≤ 5 / 12 * y := by
    have h1 := Finset.card_biUnion_le (s := Finset.Icc 3 y)
      (t := fun n => (Finset.Icc 1 y).filter (fun s => n ^ 2 ∣ s))
    have h2 : ∀ n ∈ Finset.Icc 3 y, (((Finset.Icc 1 y).filter (fun s => n ^ 2 ∣ s)).card : ℝ) ≤
        (y : ℝ) * (1 / ((n : ℝ) ^ 2 - 1)) := by
      intro n hn
      have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hcount : ((Finset.Icc 1 y).filter (fun s => n ^ 2 ∣ s)).card = y / n ^ 2 := by
        have := Nat.Ioc_filter_dvd_card_eq_div y (n ^ 2)
        rw [← this]
        have hI : Finset.Icc 1 y = Finset.Ioc 0 y := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
        rw [hI]
      rw [hcount]
      calc ((y / n ^ 2 : ℕ) : ℝ) ≤ (y : ℝ) / ((n ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
        _ ≤ (y : ℝ) * (1 / ((n : ℝ) ^ 2 - 1)) := by
          push_cast
          rw [mul_one_div]
          apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by nlinarith) (by linarith)
    have h3 : (Bad.card : ℝ) ≤ ∑ n ∈ Finset.Icc 3 y,
        (((Finset.Icc 1 y).filter (fun s => n ^ 2 ∣ s)).card : ℝ) := by exact_mod_cast h1
    rcases Nat.lt_or_ge y 2 with hy | hy
    · have : Finset.Icc 3 y = ∅ := Finset.Icc_eq_empty (by omega)
      have hB : Bad = ∅ := by simp [Bad, this]
      rw [hB]; simp
    calc (Bad.card : ℝ) ≤ _ := h3
      _ ≤ ∑ n ∈ Finset.Icc 3 y, (y : ℝ) * (1 / ((n : ℝ) ^ 2 - 1)) := Finset.sum_le_sum h2
      _ = (y : ℝ) * ∑ n ∈ Finset.Icc 3 y, (1 / ((n : ℝ) ^ 2 - 1)) := by rw [Finset.mul_sum]
      _ ≤ (y : ℝ) * (5 / 12) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact sum_inv_sq_sub_one_le y hy
      _ = 5 / 12 * y := by ring
  have hOdd : (y : ℝ) / 2 ≤ (Odd'.card : ℝ) := by
    have himg : (Finset.range ((y + 1) / 2)).image (fun k => 2 * k + 1) ⊆ Odd' := by
      intro s hs
      rw [Finset.mem_image] at hs
      obtain ⟨k, hk, rfl⟩ := hs
      rw [Finset.mem_range] at hk
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, by omega⟩
    have hinj : Set.InjOn (fun k => 2 * k + 1) (Finset.range ((y + 1) / 2) : Set ℕ) := by
      intro a _ b _ h; simp only at h; omega
    have := Finset.card_le_card himg
    rw [Finset.card_image_of_injOn hinj, Finset.card_range] at this
    have h2 : (y : ℝ) / 2 ≤ (((y + 1) / 2 : ℕ) : ℝ) := by
      have := Nat.div_add_mod (y + 1) 2
      have hm := Nat.mod_lt (y + 1) (show 0 < 2 by norm_num)
      have : ((y + 1 : ℕ) : ℝ) = 2 * (((y + 1) / 2 : ℕ) : ℝ) + (((y + 1) % 2 : ℕ) : ℝ) := by
        exact_mod_cast this.symm
      have : (((y + 1) % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (show (y + 1) % 2 ≤ 1 by omega)
      push_cast at *
      linarith
    exact le_trans h2 (by exact_mod_cast this)
  have : (Odd'.card : ℝ) ≤ (((Finset.Icc 1 y).filter (fun s => ¬ 2 ∣ s ∧ Squarefree s)).card : ℝ) +
      Bad.card := by exact_mod_cast hc1
  linarith

/-- Even squarefree numbers. -/
def EvenSqf : Set ℕ := {r | 2 ∣ r ∧ Squarefree r}

open Classical in
theorem card_evenSqf_ge (t : ℕ) :
    (t : ℝ) / 24 - 2 ≤ (((Finset.Icc 1 t).filter (fun r => r ∈ EvenSqf)).card : ℝ) := by
  classical
  have hodd := card_odd_squarefree_ge (t / 2)
  have himg : ((Finset.Icc 1 (t / 2)).filter (fun s => ¬ 2 ∣ s ∧ Squarefree s)).image (fun s => 2 * s)
      ⊆ (Finset.Icc 1 t).filter (fun r => r ∈ EvenSqf) := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hs
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, dvd_mul_right 2 s, ?_⟩
    rw [Nat.squarefree_mul_iff]
    exact ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hs.2.1, Nat.squarefree_two, hs.2.2⟩
  have hinj : Set.InjOn (fun s => 2 * s)
      (((Finset.Icc 1 (t / 2)).filter (fun s => ¬ 2 ∣ s ∧ Squarefree s)) : Set ℕ) := by
    intro a _ b _ h; simp only at h; omega
  have hc := Finset.card_le_card himg
  rw [Finset.card_image_of_injOn hinj] at hc
  have h2 : (t : ℝ) / 2 - 1 ≤ ((t / 2 : ℕ) : ℝ) := by
    have := Nat.div_add_mod t 2
    have hm := Nat.mod_lt t (show 0 < 2 by norm_num)
    have : (t : ℝ) = 2 * ((t / 2 : ℕ) : ℝ) + ((t % 2 : ℕ) : ℝ) := by exact_mod_cast this.symm
    have : ((t % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast hm
    linarith
  have : ((((Finset.Icc 1 (t / 2)).filter (fun s => ¬ 2 ∣ s ∧ Squarefree s)).card : ℕ) : ℝ) ≤
      (((Finset.Icc 1 t).filter (fun r => r ∈ EvenSqf)).card : ℝ) := by exact_mod_cast hc
  linarith

/-! ## Abel summation lower bound -/

theorem sum_Icc_inv_mul_succ (r R : ℕ) (hr : 1 ≤ r) (hrR : r ≤ R + 1) :
    ∑ t ∈ Finset.Icc r R, (1 : ℝ) / ((t : ℝ) * (t + 1)) = 1 / r - 1 / (R + 1) := by
  induction R with
  | zero =>
    have : r = 1 := by omega
    subst this
    simp
  | succ R ih =>
    by_cases h : r ≤ R + 1
    · rw [Finset.sum_Icc_succ_top (by omega), ih h]
      have : (0 : ℝ) < R + 1 := by positivity
      push_cast
      field_simp
      ring
    · have hr' : r = R + 2 := by omega
      subst hr'
      rw [Finset.Icc_eq_empty (by omega)]
      push_cast; ring

open Classical in
/-- If `#(B ∩ [1,t]) ≥ c t - c₀` for every `t`, then `∑_{r ∈ B, r ≤ R} 1/r ≥ c log (R+1) - c - c₀`. -/
theorem sum_inv_ge_of_density {B : Set ℕ} {c c₀ : ℝ} (hc : 0 ≤ c) (hc₀ : 0 ≤ c₀)
    (hB : ∀ t : ℕ, c * t - c₀ ≤ (((Finset.Icc 1 t).filter (fun r => r ∈ B)).card : ℝ)) (R : ℕ) :
    c * Real.log (R + 1) - c - c₀ ≤
      ∑ r ∈ (Finset.Icc 1 R).filter (fun r => r ∈ B), (1 : ℝ) / r := by
  classical
  set S := (Finset.Icc 1 R).filter (fun r => r ∈ B)
  have h1 : ∀ r ∈ S, ∑ t ∈ Finset.Icc 1 R, (if r ≤ t then (1 : ℝ) / ((t : ℝ) * (t + 1)) else 0)
      ≤ (1 : ℝ) / r := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    rw [← Finset.sum_filter]
    have : (Finset.Icc 1 R).filter (fun t => r ≤ t) = Finset.Icc r R := by
      ext t; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [this, sum_Icc_inv_mul_succ r R hr.1.1 (by omega)]
    have : (0 : ℝ) ≤ 1 / ((R : ℝ) + 1) := by positivity
    linarith
  have h2 : ∑ r ∈ S, ∑ t ∈ Finset.Icc 1 R, (if r ≤ t then (1 : ℝ) / ((t : ℝ) * (t + 1)) else 0)
      = ∑ t ∈ Finset.Icc 1 R, (((Finset.Icc 1 t).filter (fun r => r ∈ B)).card : ℝ) *
          ((1 : ℝ) / ((t : ℝ) * (t + 1))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hset : S.filter (fun r => r ≤ t) = (Finset.Icc 1 t).filter (fun r => r ∈ B) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_Icc, S]
      rw [Finset.mem_Icc] at ht
      constructor
      · rintro ⟨⟨⟨h1, _⟩, hB⟩, hrt⟩; exact ⟨⟨h1, hrt⟩, hB⟩
      · rintro ⟨⟨h1, hrt⟩, hB⟩; exact ⟨⟨⟨h1, by omega⟩, hB⟩, hrt⟩
    rw [hset]
  have h3 : ∀ t ∈ Finset.Icc 1 R, (c * t - c₀) * ((1 : ℝ) / ((t : ℝ) * (t + 1))) ≤
      (((Finset.Icc 1 t).filter (fun r => r ∈ B)).card : ℝ) * ((1 : ℝ) / ((t : ℝ) * (t + 1))) := by
    intro t _
    exact mul_le_mul_of_nonneg_right (hB t) (by positivity)
  have h4 : ∑ t ∈ Finset.Icc 1 R, (c * t - c₀) * ((1 : ℝ) / ((t : ℝ) * (t + 1))) =
      c * ∑ t ∈ Finset.Icc 1 R, (1 : ℝ) / ((t : ℝ) + 1) -
        c₀ * ∑ t ∈ Finset.Icc 1 R, (1 : ℝ) / ((t : ℝ) * (t + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have : (1 : ℝ) ≤ t := by exact_mod_cast (Finset.mem_Icc.mp ht).1
    field_simp
  have h5 : ∑ t ∈ Finset.Icc 1 R, (1 : ℝ) / ((t : ℝ) * (t + 1)) ≤ 1 := by
    rcases Nat.eq_zero_or_pos R with h0 | h0
    · rw [h0]; simp
    rw [sum_Icc_inv_mul_succ 1 R le_rfl (by omega)]
    have : (0 : ℝ) ≤ 1 / ((R : ℝ) + 1) := by positivity
    norm_num
    try linarith
  have h6 : Real.log (R + 1) - 1 ≤ ∑ t ∈ Finset.Icc 1 R, (1 : ℝ) / ((t : ℝ) + 1) := by
    have hl := log_add_one_le_harmonic R
    have hh : (harmonic R : ℝ) = ∑ t ∈ Finset.Icc 1 R, (t : ℝ)⁻¹ := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    have hsplit : ∑ t ∈ Finset.Icc 1 R, (t : ℝ)⁻¹ =
        ∑ t ∈ Finset.Icc 1 R, (1 : ℝ) / ((t : ℝ) + 1) +
          ∑ t ∈ Finset.Icc 1 R, (1 : ℝ) / ((t : ℝ) * (t + 1)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      have : (1 : ℝ) ≤ t := by exact_mod_cast (Finset.mem_Icc.mp ht).1
      field_simp
      try ring
    push_cast at hl
    linarith
  calc c * Real.log (R + 1) - c - c₀
      ≤ c * ∑ t ∈ Finset.Icc 1 R, (1 : ℝ) / ((t : ℝ) + 1) -
          c₀ * ∑ t ∈ Finset.Icc 1 R, (1 : ℝ) / ((t : ℝ) * (t + 1)) := by
        have := mul_le_mul_of_nonneg_left h6 hc
        have := mul_le_mul_of_nonneg_left h5 hc₀
        nlinarith
    _ = ∑ t ∈ Finset.Icc 1 R, (c * t - c₀) * ((1 : ℝ) / ((t : ℝ) * (t + 1))) := h4.symm
    _ ≤ ∑ t ∈ Finset.Icc 1 R, (((Finset.Icc 1 t).filter (fun r => r ∈ B)).card : ℝ) *
          ((1 : ℝ) / ((t : ℝ) * (t + 1))) := Finset.sum_le_sum h3
    _ = ∑ r ∈ S, ∑ t ∈ Finset.Icc 1 R,
          (if r ≤ t then (1 : ℝ) / ((t : ℝ) * (t + 1)) else 0) := h2.symm
    _ ≤ ∑ r ∈ S, (1 : ℝ) / r := Finset.sum_le_sum h1

end Erdos374.D35

end
