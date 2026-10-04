import E374.Consecutive

/-!
# D4 has positive lower density (`D4(X) ≍ X`)

Classical construction (Erdős–Graham, p. 346): if `m = 4u` with `u ≥ 2` then
`(u-1)! u! (m-1)! m! = (2u (u-1)! (m-1)!)²`, so `F(m) ≤ 4`. Among these, the endpoints with
`F(m) ∈ {2, 3}` are squares, in `ConsAll`, or in `ESet`; the last two have density zero by
`ConsAll_densityZero` (growth) and `ESet_densityZero` (RM + growth). Hence
`liminf D4(X)/X ≥ 1/4`.
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

namespace Erdos374

/-- `F(m) = 4`, in the style of the project's `D6`. -/
def D4 : Set ℕ :=
  {m | 1 < m ∧ HasRep m 4 ∧ ∀ k : ℕ, 2 ≤ k → k < 4 → ¬ HasRep m k}

namespace D35

theorem hasRep_four_of_four_dvd {m : ℕ} (h4 : 4 ∣ m) (h8 : 8 ≤ m) : HasRep m 4 := by
  obtain ⟨u, rfl⟩ := h4
  have hu : 2 ≤ u := by omega
  rw [hasRep_four_iff]
  refine ⟨u - 1, u, 4 * u - 1, by omega, by omega, by omega, by omega, ?_⟩
  refine ⟨2 * u * (u - 1).factorial * (4 * u - 1).factorial, ?_⟩
  have e1 : u.factorial = u * (u - 1).factorial := by
    conv_lhs => rw [show u = (u - 1) + 1 by omega]
    rw [Nat.factorial_succ, show u - 1 + 1 = u by omega]
  have e2 : (4 * u).factorial = (4 * u) * (4 * u - 1).factorial := by
    conv_lhs => rw [show 4 * u = (4 * u - 1) + 1 by omega]
    rw [Nat.factorial_succ, show 4 * u - 1 + 1 = 4 * u by omega]
  rw [e1, e2]
  ring

/-- Non-square multiples of 4, at least 8. -/
def M4 : Set ℕ := {m | 4 ∣ m ∧ 8 ≤ m ∧ ¬ IsSquare m}

theorem M4_diff_D4_subset : M4 \ D4 ⊆ ESet ∪ ConsAll := by
  intro m hm
  obtain ⟨⟨h4, h8, hsq⟩, hnot⟩ := hm
  have hrep := hasRep_four_of_four_dvd h4 h8
  have : ∃ k, 2 ≤ k ∧ k < 4 ∧ HasRep m k := by
    by_contra hc
    push_neg at hc
    exact hnot ⟨by omega, hrep, fun k hk hk4 => hc k hk hk4⟩
  obtain ⟨k, hk, hk4, hk'⟩ := this
  interval_cases k
  · rcases two_rep_cases hk' with h | h
    · exact absurd h hsq
    · exact Or.inl h
  · rcases three_rep_cases hk' with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem prefixCount_M4_ge (X : ℕ) :
    (X : ℝ) / 4 - 2 - Real.sqrt X ≤ (prefixCount M4 X : ℝ) := by
  classical
  set S4 := (Finset.Icc 2 (X / 4)).image (fun u => 4 * u) with hS4
  have hinj : Set.InjOn (fun u => 4 * u) (Finset.Icc 2 (X / 4) : Set ℕ) := by
    intro x _ y _ hxy; simp only at hxy; omega
  have hS4card : S4.card = X / 4 + 1 - 2 := by
    rw [hS4, Finset.card_image_of_injOn hinj, Nat.card_Icc]
  have hsub : S4.filter (fun m => ¬ IsSquare m) ⊆ (Finset.Icc 1 X).filter (fun m => m ∈ M4) := by
    intro m hm
    rw [Finset.mem_filter, hS4, Finset.mem_image] at hm
    obtain ⟨⟨u, hu, rfl⟩, hsq⟩ := hm
    rw [Finset.mem_Icc] at hu
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ⟨u, rfl⟩, by omega, hsq⟩
  have hsqsub : S4.filter (fun m => IsSquare m) ⊆ (Finset.Icc 1 X).filter (fun m => m ∈ Squares) := by
    intro m hm
    rw [Finset.mem_filter, hS4, Finset.mem_image] at hm
    obtain ⟨⟨u, hu, rfl⟩, hsq⟩ := hm
    rw [Finset.mem_Icc] at hu
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hsq⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := S4) (fun m => IsSquare m)
  have h1 : (S4.filter (fun m => IsSquare m)).card ≤ prefixCount Squares X := by
    unfold prefixCount; exact Finset.card_le_card hsqsub
  have h2 : (S4.filter (fun m => ¬ IsSquare m)).card ≤ prefixCount M4 X := by
    unfold prefixCount; exact Finset.card_le_card hsub
  have h3 := prefixCount_Squares_le X
  have h4 : (X : ℝ) / 4 - 1 ≤ ((X / 4 : ℕ) : ℝ) := by
    have := Nat.div_add_mod X 4
    have hm := Nat.mod_lt X (show 0 < 4 by norm_num)
    have : (X : ℝ) = 4 * ((X / 4 : ℕ) : ℝ) + ((X % 4 : ℕ) : ℝ) := by exact_mod_cast this.symm
    have : ((X % 4 : ℕ) : ℝ) < 4 := by exact_mod_cast hm
    linarith
  have h5 : ((X / 4 : ℕ) : ℝ) - 1 ≤ (S4.card : ℝ) := by
    rw [hS4card]
    have : X / 4 - 1 ≤ X / 4 + 1 - 2 := by omega
    calc ((X / 4 : ℕ) : ℝ) - 1 ≤ ((X / 4 - 1 : ℕ) : ℝ) := by
          rcases Nat.eq_zero_or_pos (X / 4) with h0 | h0
          · rw [h0]; simp
          · rw [Nat.cast_sub (by omega)]; simp
      _ ≤ _ := by exact_mod_cast this
  have : (S4.card : ℝ) = (S4.filter (fun m => IsSquare m)).card +
      (S4.filter (fun m => ¬ IsSquare m)).card := by exact_mod_cast hsplit.symm
  have h1' : ((S4.filter (fun m => IsSquare m)).card : ℝ) ≤ prefixCount Squares X := by
    exact_mod_cast h1
  have h2' : ((S4.filter (fun m => ¬ IsSquare m)).card : ℝ) ≤ prefixCount M4 X := by
    exact_mod_cast h2
  linarith

open Classical in
/-- **D4 has lower density at least 1/4.** -/
theorem D4_lowerDensity (hRM : Tasks.ValuationOneMass) (hG : Tasks.FactorialClassGrowth) :
    LowerDensityAtLeast D4 (1 / 4) := by
  have hbad : DensityZero (ESet ∪ ConsAll) :=
    densityZero_union (ESet_densityZero hRM hG) (ConsAll_densityZero hG)
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hbad (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := nat_eventually_rpow_dom (show (1 : ℝ) / 2 < 1 by norm_num) (8 / ε)
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (16 / ε)
  refine ⟨max (max N₁ N₂) (max N₃ 1), fun X hX => ?_⟩
  have hX1 : N₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2 : N₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3 : N₃ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX0 : 1 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hb := hN₁ X hX1
  rw [sub_zero, abs_of_nonneg (proportion_nonneg _ X)] at hb
  have hpart := prefixCount_partition D4 M4 X
  have hmono1 : prefixCount (D4 ∩ M4) X ≤ prefixCount D4 X :=
    prefixCount_mono Set.inter_subset_left X
  have hmono2 : prefixCount (M4 \ D4) X ≤ prefixCount (ESet ∪ ConsAll) X :=
    prefixCount_mono M4_diff_D4_subset X
  have hM4 := prefixCount_M4_ge X
  have hsq : Real.sqrt X ≤ ε / 8 * X := by
    have h := hN₂ X hX2
    rw [Real.rpow_one, ← Real.sqrt_eq_rpow] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    have := mul_lt_mul_of_pos_left h hε
    rw [← mul_assoc, mul_div_cancel₀ _ hε.ne'] at this
    linarith
  have h2 : 2 ≤ ε / 8 * X := by
    have : (16 / ε : ℝ) < X := lt_of_lt_of_le hN₃ (by exact_mod_cast hX3)
    rw [div_lt_iff₀ hε] at this
    linarith
  unfold proportion at hb ⊢
  rw [div_lt_iff₀ hXR] at hb
  rw [le_div_iff₀ hXR]
  have e1 : (prefixCount (D4 ∩ M4) X : ℝ) + prefixCount (M4 \ D4) X = prefixCount M4 X := by
    exact_mod_cast hpart
  have e2 : (prefixCount (D4 ∩ M4) X : ℝ) ≤ prefixCount D4 X := by exact_mod_cast hmono1
  have e3 : (prefixCount (M4 \ D4) X : ℝ) ≤ prefixCount (ESet ∪ ConsAll) X := by
    exact_mod_cast hmono2
  nlinarith

open Classical in
/-- **`D4(X) ≍ X`**: positive lower density, and trivially `D4(X) ≤ X`. -/
theorem D4_order (hRM : Tasks.ValuationOneMass) (hG : Tasks.FactorialClassGrowth) :
    PositiveLowerDensity D4 ∧ ∀ X : ℕ, prefixCount D4 X ≤ X := by
  refine ⟨⟨1 / 4, by norm_num, D4_lowerDensity hRM hG⟩, fun X => ?_⟩
  unfold prefixCount
  calc _ ≤ (Finset.Icc 1 X).card := Finset.card_filter_le _ _
    _ = X := by simp

end D35

end Erdos374

end
