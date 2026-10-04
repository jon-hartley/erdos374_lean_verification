import E374.ESet
import E374.EBounds

/-!
# Consecutive-index endpoints and the reduction of two- and three-factor representations

`ConsAll = {m : ∃ a < m, q_a * m = □}` contains every endpoint of a three-factor
representation whose two largest indices are consecutive. Every 2- or 3-factor
endpoint is a square, lies in `ConsAll`, or lies in `ESet`.
`ConsAll` has `O(√X log X)` members up to `X` (RM-free; growth only).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000

noncomputable section
open scoped BigOperators
open Finset

namespace Erdos374.D35

/-- Consecutive endpoints (no ordering refinement). -/
def ConsAll : Set ℕ := {m | ∃ a : ℕ, a < m ∧ IsSquare (q a * m)}

/-- Squares. -/
def Squares : Set ℕ := {m | IsSquare m}

/-- A two-factor endpoint is a square or lies in `ESet`. -/
theorem two_rep_cases {m : ℕ} (h : HasRep m 2) : m ∈ Squares ∨ m ∈ ESet := by
  obtain ⟨ℓ, hℓ, hℓm, hs⟩ := hasRep_two_iff_falling.mp h
  rcases Nat.lt_or_ge ℓ 2 with h1 | h2
  · left
    have : ℓ = 1 := by omega
    subst this
    show IsSquare m
    simpa [falling] using hs
  · right
    exact ⟨0, ℓ, h2, by omega, by rw [q_zero', one_mul]; exact hs⟩

/-- A three-factor endpoint lies in `ConsAll` or in `ESet`. -/
theorem three_rep_cases {m : ℕ} (h : HasRep m 3) : m ∈ ConsAll ∨ m ∈ ESet := by
  obtain ⟨a, k, ha, hk, hakm, hs⟩ := hasRep_three_iff_reduced.mp h
  rcases Nat.lt_or_ge k 2 with h1 | h2
  · left
    have : k = 1 := by omega
    subst this
    exact ⟨a, by omega, by simpa [falling] using hs⟩
  · right
    exact ⟨a, k, h2, hakm, hs⟩

/-- `q a * m = □` forces `m = q_a u²`. -/
theorem eq_q_mul_sq_of_isSquare {a m : ℕ} (hs : IsSquare (q a * m)) :
    ∃ u : ℕ, m = q a * u ^ 2 := by
  obtain ⟨k, hk⟩ := q_dvd_of_isSquare hs
  rw [hk, ← mul_assoc] at hs
  obtain ⟨u, hu⟩ := isSquare_of_mul_sq (q_ne_zero a) hs
  exact ⟨u, by rw [hk, hu]; ring⟩

/-- Indices with small kernel: `#{a ≤ X : q_a ≤ X} ≤ N₀ + 3 log X + 1`. -/
theorem card_small_kernel_indices (hG : Tasks.FactorialClassGrowth) :
    ∃ N₀ : ℕ, ∀ X : ℕ, 1 ≤ X →
      (((Finset.range (X + 1)).filter (fun a => q a ≤ X)).card : ℝ) ≤ N₀ + 3 * Real.log X + 1 := by
  classical
  obtain ⟨N₀, hN₀⟩ := hG
  refine ⟨N₀, fun X hX => ?_⟩
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hsub : (Finset.range (X + 1)).filter (fun a => q a ≤ X) ⊆
      Finset.range N₀ ∪ Finset.range (⌊3 * Real.log X⌋₊ + 1) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_range]
    by_cases haN : N₀ ≤ a
    · right
      have h1 := hN₀ a haN
      have h2 : Real.exp ((a : ℝ) / 3) ≤ X := le_trans h1 (by exact_mod_cast ha.2)
      have h3 : (a : ℝ) / 3 ≤ Real.log X := by
        have := Real.log_le_log (Real.exp_pos _) h2
        rwa [Real.log_exp] at this
      have : a ≤ ⌊3 * Real.log X⌋₊ := Nat.le_floor (by linarith)
      omega
    · left; omega
  have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  rw [Finset.card_range, Finset.card_range] at hc
  have hfl : (⌊3 * Real.log X⌋₊ : ℝ) ≤ 3 * Real.log X :=
    Nat.floor_le (by have := Real.log_nonneg hX1R; positivity)
  calc (((Finset.range (X + 1)).filter (fun a => q a ≤ X)).card : ℝ)
      ≤ ((N₀ + (⌊3 * Real.log X⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ N₀ + 3 * Real.log X + 1 := by push_cast; linarith

/-- **`ConsAll` count**: `≤ (N₀ + 3 log X + 1)(√X + 1)`. -/
theorem prefixCount_ConsAll_le (hG : Tasks.FactorialClassGrowth) :
    ∃ N₀ : ℕ, ∀ X : ℕ, 1 ≤ X →
      (prefixCount ConsAll X : ℝ) ≤ (N₀ + 3 * Real.log X + 1) * (Real.sqrt X + 1) := by
  classical
  obtain ⟨N₀, hN₀⟩ := card_small_kernel_indices hG
  refine ⟨N₀, fun X hX => ?_⟩
  set A := (Finset.range (X + 1)).filter (fun a => q a ≤ X)
  have hsub : (Finset.Icc 1 X).filter (fun m => m ∈ ConsAll) ⊆
      A.biUnion (fun a => (Finset.range (Nat.sqrt X + 1)).image (fun u => q a * u ^ 2)) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmX⟩, a, ham, hs⟩ := hm
    obtain ⟨u, hu⟩ := eq_q_mul_sq_of_isSquare hs
    have hq1 : 1 ≤ q a := q_pos a
    have hu2 : u ^ 2 ≤ X := by
      have : u ^ 2 ≤ q a * u ^ 2 := Nat.le_mul_of_pos_left _ hq1
      omega
    have hqX : q a ≤ X := by
      have hu0 : 1 ≤ u ^ 2 := by
        rcases Nat.eq_zero_or_pos u with h0 | h0
        · rw [h0] at hu; simp at hu; omega
        · exact Nat.one_le_pow _ _ h0
      have : q a ≤ q a * u ^ 2 := Nat.le_mul_of_pos_right _ hu0
      omega
    rw [Finset.mem_biUnion]
    refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hqX⟩
    · rw [Finset.mem_image]
      exact ⟨u, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_sqrt'.mpr hu2)), hu.symm⟩
  have hc := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hfib : ∀ a ∈ A, ((Finset.range (Nat.sqrt X + 1)).image (fun u => q a * u ^ 2)).card ≤
      Nat.sqrt X + 1 := by
    intro a _
    exact le_trans Finset.card_image_le (by rw [Finset.card_range])
  have hc2 : prefixCount ConsAll X ≤ A.card * (Nat.sqrt X + 1) := by
    unfold prefixCount
    calc _ ≤ _ := hc
      _ ≤ ∑ _a ∈ A, (Nat.sqrt X + 1) := Finset.sum_le_sum hfib
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  have hsq : (Nat.sqrt X : ℝ) ≤ Real.sqrt X := Real.nat_sqrt_le_real_sqrt
  have hA := hN₀ X hX
  calc (prefixCount ConsAll X : ℝ) ≤ ((A.card * (Nat.sqrt X + 1) : ℕ) : ℝ) := by exact_mod_cast hc2
    _ = (A.card : ℝ) * ((Nat.sqrt X : ℝ) + 1) := by push_cast; ring
    _ ≤ (N₀ + 3 * Real.log X + 1) * (Real.sqrt X + 1) := by
        apply mul_le_mul hA (by linarith) (by positivity)
        have := Real.log_nonneg (show (1 : ℝ) ≤ X by exact_mod_cast hX)
        positivity

theorem ConsAll_densityZero (hG : Tasks.FactorialClassGrowth) : DensityZero ConsAll := by
  obtain ⟨N₀, hN₀⟩ := prefixCount_ConsAll_le hG
  obtain ⟨N₁, hN₁⟩ := nat_eventually_rpow_log_dom (show (1 : ℝ) / 2 < 3 / 4 by norm_num)
    (2 * (N₀ + 4))
  obtain ⟨N₂, hN₂⟩ := nat_eventually_log_gt 1
  refine densityZero_of_power_bound (C := 1) (δ := (3 : ℝ) / 4) (N := max N₁ (max N₂ 3))
    (by norm_num) (fun X hX => ?_)
  have hX3 : 3 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hlog1 : 1 ≤ Real.log X := (hN₂ X (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX))).le
  have h1 := hN₀ X (by omega)
  have h2 := hN₁ X (le_trans (le_max_left _ _) hX)
  have hsq : Real.sqrt X + 1 ≤ 2 * (X : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    have : (1 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hX1R (by norm_num)
    linarith
  have hN0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  have hA : (N₀ : ℝ) + 3 * Real.log X + 1 ≤ (N₀ + 4) * Real.log X := by nlinarith
  have hs0 : 0 ≤ (X : ℝ) ^ ((1 : ℝ) / 2) := by positivity
  calc (prefixCount ConsAll X : ℝ) ≤ (N₀ + 3 * Real.log X + 1) * (Real.sqrt X + 1) := h1
    _ ≤ ((N₀ + 4) * Real.log X) * (2 * (X : ℝ) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul hA hsq (by positivity) (by nlinarith)
    _ = 2 * (N₀ + 4) * (X : ℝ) ^ ((1 : ℝ) / 2) * Real.log X := by ring
    _ ≤ (X : ℝ) ^ ((3 : ℝ) / 4) := h2.le
    _ = 1 * (X : ℝ) ^ ((3 : ℝ) / 4) := by ring

/-- Squares have density zero. -/
theorem prefixCount_Squares_le (X : ℕ) : (prefixCount Squares X : ℝ) ≤ Real.sqrt X := by
  classical
  have hsub : (Finset.Icc 1 X).filter (fun m => m ∈ Squares) ⊆
      (Finset.Icc 1 (Nat.sqrt X)).image (fun u => u ^ 2) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmX⟩, u, hu⟩ := hm
    rw [Finset.mem_image]
    refine ⟨u, Finset.mem_Icc.mpr ⟨?_, Nat.le_sqrt.mpr (by omega)⟩, by rw [hu]; ring⟩
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0] at hu; omega
    · exact h0
  have hc := le_trans (Finset.card_le_card hsub) Finset.card_image_le
  rw [Nat.card_Icc] at hc
  have : prefixCount Squares X ≤ Nat.sqrt X := by unfold prefixCount; omega
  calc (prefixCount Squares X : ℝ) ≤ (Nat.sqrt X : ℝ) := by exact_mod_cast this
    _ ≤ Real.sqrt X := Real.nat_sqrt_le_real_sqrt

end Erdos374.D35

end
