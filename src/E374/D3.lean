import E374.Consecutive
import E374.EBoundsWeil
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# `D3(X) ≍ √X`

* Lower bound: for `m = 2u²` (`u ≥ 2`), `2! (m-1)! m! = (2u (m-1)!)²` and `m` is not a square,
  so `F(m) = 3` unless `m ∈ ESet`.
* Upper bound: every 3-factor endpoint lies in `ConsAll` or `ESet`, and
  `#ConsAll(X) ≤ (N₀ + (1 - e^{-1/6})⁻¹) √X` because `q_a ≥ e^{a/3}`.
* `E(X) ≪ X^{9/20} = o(√X)` (`ESet_count_le`).

Inputs: RM, growth, coarse Weil (all proved in the project). No Pell-type input is assumed:
the small-kernel case uses the elementary class count `pell_count_le`.
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

/-! ## `#ConsAll(X) = O(√X)` -/

theorem prefixCount_ConsAll_le_sqrt (hG : Tasks.FactorialClassGrowth) :
    ∃ K : ℝ, ∀ X : ℕ, 1 ≤ X → (prefixCount ConsAll X : ℝ) ≤ K * Real.sqrt X := by
  classical
  obtain ⟨N₀, hN₀⟩ := hG
  set r : ℝ := Real.exp (-(1 / 6)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; norm_num
  refine ⟨N₀ + (1 - r)⁻¹, fun X hX => ?_⟩
  set g : ℕ → ℝ := fun a => if a < N₀ then 1 else r ^ a with hg
  set A := (Finset.range (X + 1)).filter (fun a => q a ≤ X)
  have hsub : (Finset.Icc 1 X).filter (fun m => m ∈ ConsAll) ⊆
      A.biUnion (fun a => (Finset.Icc 1 (Nat.sqrt (X / q a))).image (fun u => q a * u ^ 2)) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmX⟩, a, ham, hs⟩ := hm
    obtain ⟨u, hu⟩ := eq_q_mul_sq_of_isSquare hs
    have hq1 : 1 ≤ q a := q_pos a
    have hu1 : 1 ≤ u := by
      rcases Nat.eq_zero_or_pos u with h0 | h0
      · rw [h0] at hu; simp at hu; omega
      · exact h0
    have hqX : q a ≤ X := by
      have : q a ≤ q a * u ^ 2 := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hu1)
      omega
    have hu2 : u ^ 2 ≤ X / q a := by
      rw [Nat.le_div_iff_mul_le hq1]; rw [mul_comm]; omega
    rw [Finset.mem_biUnion]
    refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hqX⟩
    · rw [Finset.mem_image]
      exact ⟨u, Finset.mem_Icc.mpr ⟨hu1, Nat.le_sqrt'.mpr hu2⟩, hu.symm⟩
  have hc := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hfib : ∀ a ∈ A, (((Finset.Icc 1 (Nat.sqrt (X / q a))).image (fun u => q a * u ^ 2)).card : ℝ)
      ≤ Real.sqrt X * g a := by
    intro a _
    have h1 : (((Finset.Icc 1 (Nat.sqrt (X / q a))).image (fun u => q a * u ^ 2)).card : ℝ) ≤
        (Nat.sqrt (X / q a) : ℝ) := by
      have := le_trans (Finset.card_image_le (s := Finset.Icc 1 (Nat.sqrt (X / q a)))
        (f := fun u => q a * u ^ 2)) (le_of_eq (Nat.card_Icc 1 (Nat.sqrt (X / q a))))
      have : ((Finset.Icc 1 (Nat.sqrt (X / q a))).image (fun u => q a * u ^ 2)).card ≤
          Nat.sqrt (X / q a) := by omega
      exact_mod_cast this
    have hq0 : (0 : ℝ) < q a := by exact_mod_cast q_pos a
    have h2 : (Nat.sqrt (X / q a) : ℝ) ≤ Real.sqrt X / Real.sqrt (q a) := by
      calc (Nat.sqrt (X / q a) : ℝ) ≤ Real.sqrt ((X / q a : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
        _ ≤ Real.sqrt ((X : ℝ) / q a) := Real.sqrt_le_sqrt Nat.cast_div_le
        _ = Real.sqrt X / Real.sqrt (q a) := Real.sqrt_div' _ hq0.le
    have h3 : Real.sqrt X / Real.sqrt (q a) ≤ Real.sqrt X * g a := by
      rw [hg]
      by_cases ha : a < N₀
      · simp only [if_pos ha, mul_one]
        apply div_le_self (Real.sqrt_nonneg _)
        rw [Real.one_le_sqrt]; exact_mod_cast q_pos a
      · simp only [if_neg ha]
        push_neg at ha
        have hexp := hN₀ a ha
        have hsq : Real.exp ((a : ℝ) / 6) ≤ Real.sqrt (q a) := by
          rw [Real.le_sqrt (Real.exp_pos _).le hq0.le, ← Real.exp_nat_mul]
          · convert hexp using 2; push_cast; ring
        have hra : r ^ a = (Real.exp ((a : ℝ) / 6))⁻¹ := by
          rw [hr, ← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; ring
        rw [hra, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact inv_anti₀ (Real.exp_pos _) hsq
    exact le_trans h1 (le_trans h2 h3)
  have hgsum : ∑ a ∈ A, g a ≤ N₀ + (1 - r)⁻¹ := by
    have hgnn : ∀ a, 0 ≤ g a := fun a => by simp only [hg]; split_ifs <;> positivity
    calc ∑ a ∈ A, g a ≤ ∑ a ∈ Finset.range (X + 1), g a :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a _ _ => hgnn a)
      _ ≤ ∑ a ∈ Finset.range (X + 1), ((if a < N₀ then (1 : ℝ) else 0) + r ^ a) := by
          apply Finset.sum_le_sum; intro a _
          simp only [hg]; split_ifs <;> simp [hr0.le, pow_nonneg]
          all_goals positivity
      _ = ∑ a ∈ Finset.range (X + 1), (if a < N₀ then (1 : ℝ) else 0) +
            ∑ a ∈ Finset.range (X + 1), r ^ a := Finset.sum_add_distrib
      _ ≤ N₀ + (1 - r)⁻¹ := by
          apply add_le_add
          · rw [Finset.sum_boole]
            have : ((Finset.range (X + 1)).filter (fun a => a < N₀)).card ≤ N₀ := by
              calc _ ≤ (Finset.range N₀).card := Finset.card_le_card (by
                    intro a ha; rw [Finset.mem_filter] at ha; exact Finset.mem_range.mpr ha.2)
                _ = N₀ := Finset.card_range _
            exact_mod_cast this
          · exact geom_sum_le_inv hr0.le hr1 _
  have hc' : prefixCount ConsAll X ≤
      ∑ a ∈ A, ((Finset.Icc 1 (Nat.sqrt (X / q a))).image (fun u => q a * u ^ 2)).card := by
    unfold prefixCount; convert hc using 2
  calc (prefixCount ConsAll X : ℝ)
      ≤ ((∑ a ∈ A, ((Finset.Icc 1 (Nat.sqrt (X / q a))).image (fun u => q a * u ^ 2)).card : ℕ) : ℝ) := by
        exact_mod_cast hc'
    _ = ∑ a ∈ A, (((Finset.Icc 1 (Nat.sqrt (X / q a))).image (fun u => q a * u ^ 2)).card : ℝ) := by
        push_cast; rfl
    _ ≤ ∑ a ∈ A, Real.sqrt X * g a := Finset.sum_le_sum hfib
    _ = Real.sqrt X * ∑ a ∈ A, g a := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt X * (N₀ + (1 - r)⁻¹) := mul_le_mul_of_nonneg_left hgsum (Real.sqrt_nonneg _)
    _ = (N₀ + (1 - r)⁻¹) * Real.sqrt X := by ring

/-! ## The explicit family `2u²` -/

theorem not_isSquare_two {n : ℕ} (hn : n ≠ 0) : ¬ IsSquare (2 * n ^ 2) := by
  intro hs
  have h2 := (Nat.isSquare_iff_even_factorization.mp hs) 2 Nat.prime_two
  rw [Nat.factorization_mul (by norm_num) (pow_ne_zero 2 hn), Nat.factorization_pow] at h2
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
    Nat.Prime.factorization_self Nat.prime_two] at h2
  rw [Nat.even_iff] at h2
  omega

theorem q_two : q 2 = 2 := by
  have hd : q 2 ∣ 2 := by simpa using q_dvd_factorial 2
  have hle : q 2 ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  have hpos := q_pos 2
  have hsq : IsSquare (q 2 * 2) := by
    rw [isSquare_q_mul_iff]; exact ⟨2, by norm_num [Nat.factorial]⟩
  interval_cases h : q 2
  · exfalso
    obtain ⟨r, hr⟩ := hsq
    have : r ≤ 1 := by nlinarith
    interval_cases r <;> omega
  · rfl

/-- The family `{2u² : u ≥ 2}`. -/
def Twos : Set ℕ := {m | ∃ u : ℕ, 2 ≤ u ∧ m = 2 * u ^ 2}

theorem Twos_diff_ESet_subset : Twos \ ESet ⊆ D3 := by
  rintro m ⟨⟨u, hu, rfl⟩, hE⟩
  have hm8 : 8 ≤ 2 * u ^ 2 := by nlinarith
  refine ⟨by omega, ?_, ?_⟩
  · rw [hasRep_three_iff_reduced]
    refine ⟨2, 1, by norm_num, le_refl 1, by omega, ?_⟩
    rw [q_two]
    refine ⟨2 * u, ?_⟩
    simp [falling]; ring
  · intro h2
    rcases two_rep_cases h2 with h | h
    · exact not_isSquare_two (show u ≠ 0 by omega) h
    · exact hE h

theorem prefixCount_Twos_ge (X : ℕ) :
    Real.sqrt ((X : ℝ) / 2) - 2 ≤ (prefixCount Twos X : ℝ) := by
  classical
  set k := Nat.sqrt (X / 2)
  have hinj : Set.InjOn (fun u => 2 * u ^ 2) (Finset.Icc 2 k : Set ℕ) := by
    intro x _ y _ hxy
    simp only at hxy
    have : x ^ 2 = y ^ 2 := by omega
    exact Nat.pow_left_injective (by norm_num) this
  have hsub : (Finset.Icc 2 k).image (fun u => 2 * u ^ 2) ⊆
      (Finset.Icc 1 X).filter (fun m => m ∈ Twos) := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨u, hu, rfl⟩ := hm
    rw [Finset.mem_Icc] at hu
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hu2 : u ^ 2 ≤ X / 2 := Nat.le_sqrt'.mp hu.2
    refine ⟨⟨by nlinarith, by omega⟩, u, hu.1, rfl⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Nat.card_Icc] at hc
  have h1 : Real.sqrt ((X : ℝ) / 2) ≤ k + 1 := by
    calc Real.sqrt ((X : ℝ) / 2) ≤ Real.sqrt (((X / 2 : ℕ) : ℝ) + 1) := by
          apply Real.sqrt_le_sqrt
          have := Nat.div_add_mod X 2
          have hm := Nat.mod_lt X (show 0 < 2 by norm_num)
          have : (X : ℝ) = 2 * ((X / 2 : ℕ) : ℝ) + ((X % 2 : ℕ) : ℝ) := by
            exact_mod_cast this.symm
          have : ((X % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (show X % 2 ≤ 1 by omega)
          linarith
      _ ≤ k + 1 := by
          rw [Real.sqrt_le_left (by positivity)]
          have := Nat.lt_succ_sqrt (X / 2)
          have : ((X / 2 : ℕ) : ℝ) + 1 ≤ ((k + 1) * (k + 1) : ℕ) := by exact_mod_cast this
          push_cast at this; nlinarith
  have h2 : ((k : ℝ) - 1) ≤ (prefixCount Twos X : ℝ) := by
    have : k + 1 - 2 ≤ prefixCount Twos X := by unfold prefixCount; exact hc
    rcases Nat.lt_or_ge k 1 with hk | hk
    · have : (k : ℝ) < 1 := by exact_mod_cast hk
      have := Nat.cast_nonneg (α := ℝ) (prefixCount Twos X)
      linarith
    · have : ((k + 1 - 2 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [← this]; exact_mod_cast ‹k + 1 - 2 ≤ prefixCount Twos X›
  linarith

/-- **`D3(X) ≍ √X`.** -/
theorem D3_order (hRM : Tasks.ValuationOneMass) (hG : Tasks.FactorialClassGrowth)
    (hW : CoarseWeilBound) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      Real.sqrt X / 2 ≤ (prefixCount D3 X : ℝ) ∧ (prefixCount D3 X : ℝ) ≤ C * Real.sqrt X := by
  obtain ⟨K, hK⟩ := prefixCount_ConsAll_le_sqrt hG
  obtain ⟨CE, NE, hNE⟩ := ESet_count_le hRM hG hW (1 / 20) (by norm_num)
  -- `CE X^{9/20} ≤ √X / 10` and `2 ≤ √X / 10` eventually
  obtain ⟨N₁, hN₁⟩ := nat_eventually_rpow_dom (show (2 : ℝ) / 5 + 1 / 20 < 1 / 2 by norm_num)
    (10 * max CE 0)
  obtain ⟨N₂, hN₂⟩ := nat_eventually_rpow_gt (show (0 : ℝ) < 1 / 2 by norm_num) 20
  refine ⟨K + 1, max (max NE N₁) (max N₂ 1), fun X hX => ?_⟩
  have hXE : NE ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX1' : N₁ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX2 : N₂ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX1 : 1 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hsqrt : Real.sqrt X = (X : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hE := hNE X hXE
  have hE' : (prefixCount ESet X : ℝ) ≤ Real.sqrt X / 10 := by
    have h1 := hN₁ X hX1'
    rw [← hsqrt] at h1
    have : CE * (X : ℝ) ^ ((2 : ℝ) / 5 + 1 / 20) ≤ max CE 0 * (X : ℝ) ^ ((2 : ℝ) / 5 + 1 / 20) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  have h20 : 20 < Real.sqrt X := by rw [hsqrt]; exact hN₂ X hX2
  constructor
  · -- lower bound
    have hpart := prefixCount_partition D3 Twos X
    have hm1 : prefixCount (D3 ∩ Twos) X ≤ prefixCount D3 X :=
      prefixCount_mono Set.inter_subset_left X
    have hm2 : prefixCount (Twos \ D3) X ≤ prefixCount ESet X := by
      apply prefixCount_mono
      intro m ⟨hT, hD⟩
      by_contra hE
      exact hD (Twos_diff_ESet_subset ⟨hT, hE⟩)
    have hT := prefixCount_Twos_ge X
    have e1 : (prefixCount (D3 ∩ Twos) X : ℝ) + prefixCount (Twos \ D3) X = prefixCount Twos X := by
      exact_mod_cast hpart
    have e2 : (prefixCount (D3 ∩ Twos) X : ℝ) ≤ prefixCount D3 X := by exact_mod_cast hm1
    have e3 : (prefixCount (Twos \ D3) X : ℝ) ≤ prefixCount ESet X := by exact_mod_cast hm2
    have hhalf : Real.sqrt ((X : ℝ) / 2) ≥ Real.sqrt X * (7 / 10) := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
      rw [ge_iff_le, le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
      have : Real.sqrt 2 ≤ 1.42 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have := Real.sqrt_nonneg (X : ℝ)
      nlinarith
    linarith
  · -- upper bound
    have hsub : D3 ⊆ ConsAll ∪ ESet := by
      intro m ⟨_, h3, _⟩
      rcases three_rep_cases h3 with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h1 := prefixCount_mono hsub X
    have h2 := prefixCount_union_le ConsAll ESet X
    have hc := hK X hX1
    have : (prefixCount D3 X : ℝ) ≤ prefixCount ConsAll X + prefixCount ESet X := by
      exact_mod_cast le_trans h1 h2
    have := Real.sqrt_nonneg (X : ℝ)
    nlinarith

/-- Every `D3` endpoint is either consecutive-type or in `E`. -/
theorem D3_subset_ConsAll_union : D3 ⊆ ConsAll ∪ ESet := by
  intro m ⟨_, h3, _⟩
  rcases three_rep_cases h3 with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **`D3` has density zero** — needs only RM and factorial growth (no Pell input). -/
theorem D3_densityZero (hRM : Tasks.ValuationOneMass) (hG : Tasks.FactorialClassGrowth) :
    DensityZero D3 :=
  densityZero_mono D3_subset_ConsAll_union
    (densityZero_union (ConsAll_densityZero hG) (ESet_densityZero hRM hG))

end Erdos374.D35

end
