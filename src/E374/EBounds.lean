import E374.SmallKernel
import E374.LargeKernel

/-!
# Bounds for the nonconsecutive endpoint count `E(X)`

* `ESet_densityZero` — `E(X) = o(X)`, using only RM and factorial growth
  (σ = 1/3, trivial residue sets, crude small-kernel count).
* `ESet_count_le` (in `E374.EBoundsWeil`) — `E(X) ≪ X^{2/5+ε}`, additionally using the
  coarse Weil bound and the elementary Pell class count (σ = 1/5, balancing the two kernel ranges).
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

/-! ## Elementary log/floor helpers -/

theorem log_floor_le {t : ℝ} (ht : 1 ≤ t) : Real.log (⌊t⌋₊ : ℕ) ≤ Real.log t := by
  have h1 : (1 : ℝ) ≤ (⌊t⌋₊ : ℕ) := by exact_mod_cast Nat.le_floor (by exact_mod_cast ht)
  exact Real.log_le_log (by linarith) (Nat.floor_le (by linarith))

theorem log_floor_ge {t : ℝ} (ht : 2 ≤ t) : Real.log t - Real.log 2 ≤ Real.log (⌊t⌋₊ : ℕ) := by
  have h1 : t - 1 < (⌊t⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one t; linarith
  have h2 : t / 2 ≤ (⌊t⌋₊ : ℝ) := by linarith
  have h3 : Real.log (t / 2) ≤ Real.log (⌊t⌋₊ : ℕ) := Real.log_le_log (by linarith) h2
  rw [Real.log_div (by linarith) (by norm_num)] at h3
  exact h3

theorem log_rpow_nat {X : ℕ} (hX : 1 ≤ X) (a : ℝ) :
    Real.log ((X : ℝ) ^ a) = a * Real.log X :=
  Real.log_rpow (by exact_mod_cast (show 0 < X by omega)) a

/-- `log q_a / h > σ log X` in the large-kernel regime. -/
theorem log_q_div_gt {X a h : ℕ} {σ : ℝ} (hX : 1 ≤ X) (hh : 1 ≤ h)
    (hk : ((X : ℝ) ^ σ) ^ h < (q a : ℝ)) : σ * Real.log X < Real.log (q a) / h := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hpos : 0 < ((X : ℝ) ^ σ) ^ h := by positivity
  have h1 := Real.log_lt_log hpos hk
  rw [Real.log_pow, Real.log_rpow hX0] at h1
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  rw [lt_div_iff₀ hhR]
  linarith

/-- From a power bound with exponent `< 1` to density zero. -/
theorem densityZero_of_power_bound {S : Set ℕ} {C δ : ℝ} {N : ℕ} (hδ : δ < 1)
    (hb : ∀ X : ℕ, N ≤ X → (prefixCount S X : ℝ) ≤ C * (X : ℝ) ^ δ) : DensityZero S := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := nat_eventually_rpow_dom hδ (C / ε)
  refine ⟨max (max N N₁) 1, fun X hX => ?_⟩
  have hXN : N ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXN₁ : N₁ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  rw [sub_zero, abs_of_nonneg (proportion_nonneg S X)]
  unfold proportion
  rw [div_lt_iff₀ hX0]
  have h1 := hb X hXN
  have h2 := hN₁ X hXN₁
  rw [Real.rpow_one] at h2
  have : C * (X : ℝ) ^ δ < ε * X := by
    have := mul_lt_mul_of_pos_left h2 hε
    rw [← mul_assoc, mul_div_cancel₀ _ hε.ne'] at this
    linarith
  linarith

/-! ## `E(X) = o(X)` with no analytic input beyond RM and growth -/

/-- Fibre bound in the trivial regime `σ = 1/3`, `η = 1/100`. -/
theorem fibre_card_le_trivial :
    ∃ C : ℝ, ∃ N : ℕ, ∀ X : ℕ, N ≤ X → ∀ a h : ℕ, a ≤ Hcut (1 / 100) X → 2 ≤ h →
      h ≤ Hcut (1 / 100) X → ((X : ℝ) ^ ((1 : ℝ) / 3)) ^ h < (q a : ℝ) →
      ((fibre X a h).card : ℝ) ≤ C * (X : ℝ) ^ ((71 : ℝ) / 100) := by
  obtain ⟨CM, hCM⟩ := mertens_interval
  set η : ℝ := 1 / 100
  -- eventually `η/2 log X ≥ log 8 + |CM|`, `log X ≥ 1`, `X^{0.71} ≥ 2`, `Y ≤ Q`
  obtain ⟨N₁, hN₁⟩ := nat_eventually_log_gt (2 / η * (Real.log 8 + |CM|) + 1)
  obtain ⟨N₂, hN₂⟩ := nat_eventually_rpow_gt (show (0 : ℝ) < 71 / 100 by norm_num) 2
  refine ⟨4 * Real.log 4 / η, max (max N₁ N₂) 2, fun X hX a h haH hh hhH hk => ?_⟩
  have hX1 : 1 ≤ X := le_trans (by norm_num) (le_trans (le_max_right _ _) hX)
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hX0R : (0 : ℝ) < X := by linarith
  have hlogX := hN₁ X (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX)
  have hQ2 := hN₂ X (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX)
  set Y : ℕ := ⌊(X : ℝ) ^ (3 * η)⌋₊ with hY
  set Q : ℕ := ⌊(X : ℝ) ^ ((71 : ℝ) / 100)⌋₊ with hQ
  have hHle : (Hcut η X : ℝ) ≤ (X : ℝ) ^ η := (Hcut_le (by norm_num) hX1).1
  have hHY : Hcut η X ≤ Y := by
    apply Nat.floor_le_floor
    exact Real.rpow_le_rpow_of_exponent_le hX1R (by norm_num)
  have hYQ : Y ≤ Q := by
    apply Nat.floor_le_floor
    exact Real.rpow_le_rpow_of_exponent_le hX1R (by norm_num)
  have hfb := fibre_bound_trivial (Q := Q) hX1 (by omega) (by omega : a < Y + 1)
    (by omega : h < Y + 1) CM (hCM Y Q hYQ)
  -- lower bound for the denominator
  have hlogq := log_q_div_gt hX1 (by omega) hk
  have hhR : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hsplit : (Real.log (q a) - Real.log 4 * h) / h = Real.log (q a) / h - Real.log 4 := by
    field_simp
  have hlogQ : Real.log ((X : ℝ) ^ ((71 : ℝ) / 100)) - Real.log 2 ≤ Real.log Q :=
    log_floor_ge hQ2.le
  rw [log_rpow_nat hX1] at hlogQ
  have hlogY : Real.log Y ≤ 3 * η * Real.log X := by
    rcases Nat.eq_zero_or_pos Y with h0 | h0
    · rw [h0]; simp; positivity
    · have h1 : (1 : ℝ) ≤ (X : ℝ) ^ (3 * η) := Real.one_le_rpow hX1R (by norm_num)
      have := log_floor_le h1
      rwa [log_rpow_nat hX1] at this
  have hD : η / 2 * Real.log X ≤
      (Real.log (q a) - Real.log 4 * h) / h + (Real.log Q - Real.log Y - CM) - Real.log X := by
    rw [hsplit]
    have hl8 : Real.log 8 = Real.log 4 + Real.log 2 := by
      rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have habs := le_abs_self CM
    have : η / 2 * Real.log X ≥ Real.log 8 + |CM| := by
      have hη : (0 : ℝ) < η := by norm_num
      have := hlogX
      have : (2 / η) * (Real.log 8 + |CM|) < Real.log X := by linarith
      rw [div_mul_eq_mul_div, div_lt_iff₀ hη] at this
      linarith
    have hηv : η = 1 / 100 := rfl
    rw [hηv] at hlogY this ⊢
    have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1R
    have hq3 : (1 / 3 : ℝ) * Real.log X < Real.log (q a) / h := hlogq
    linarith
  -- upper bound for the right side
  have hRHS : max (Real.log 4 * a + Real.log 4 * Q - Real.log X) 0 ≤
      2 * Real.log 4 * (X : ℝ) ^ ((71 : ℝ) / 100) := by
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have haR : (a : ℝ) ≤ (X : ℝ) ^ ((71 : ℝ) / 100) := by
      have : (a : ℝ) ≤ (X : ℝ) ^ η := le_trans (by exact_mod_cast haH) hHle
      exact le_trans this (Real.rpow_le_rpow_of_exponent_le hX1R (by norm_num))
    have hQR : (Q : ℝ) ≤ (X : ℝ) ^ ((71 : ℝ) / 100) := Nat.floor_le (by positivity)
    have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1R
    apply max_le
    · nlinarith
    · positivity
  have hlogX1 : 1 ≤ Real.log X := by
    have : 0 ≤ 2 / η * (Real.log 8 + |CM|) := by
      have : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
      positivity
    linarith
  have hJ : (0 : ℝ) ≤ (fibre X a h).card := Nat.cast_nonneg _
  have hmain : ((fibre X a h).card : ℝ) * (η / 2 * Real.log X) ≤
      2 * Real.log 4 * (X : ℝ) ^ ((71 : ℝ) / 100) :=
    le_trans (mul_le_mul_of_nonneg_left hD hJ) (le_trans hfb hRHS)
  have hpos : 0 < η / 2 * Real.log X := by norm_num [η]; linarith
  have : ((fibre X a h).card : ℝ) ≤ 2 * Real.log 4 * (X : ℝ) ^ ((71 : ℝ) / 100) / (η / 2 * Real.log X) :=
    (le_div_iff₀ hpos).mpr hmain
  calc ((fibre X a h).card : ℝ) ≤ 2 * Real.log 4 * (X : ℝ) ^ ((71 : ℝ) / 100) / (η / 2 * Real.log X) := this
    _ ≤ 2 * Real.log 4 * (X : ℝ) ^ ((71 : ℝ) / 100) / (η / 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num [η])
        norm_num [η] at *; nlinarith
    _ = 4 * Real.log 4 / η * (X : ℝ) ^ ((71 : ℝ) / 100) := by ring

/-- **`E(X) = o(X)`** (RM + factorial growth only). -/
theorem ESet_densityZero (hRM : Tasks.ValuationOneMass) (hG : Tasks.FactorialClassGrowth) :
    DensityZero ESet := by
  obtain ⟨N₀, hN₀⟩ := prefixCount_ESet_le hRM hG (η := 1 / 100) (by norm_num) (by norm_num)
    ((1 : ℝ) / 3)
  obtain ⟨C, N₁, hN₁⟩ := fibre_card_le_trivial
  refine densityZero_of_power_bound (C := 16 + 4 * max C 0) (δ := (9 : ℝ) / 10)
    (N := max (max N₀ N₁) 1) (by norm_num) (fun X hX => ?_)
  have hX0 : N₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX1' : N₁ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hX0R : (0 : ℝ) < X := by linarith
  set η : ℝ := 1 / 100
  have hdec := hN₀ X hX0
  have hH := Hcut_le (show (0 : ℝ) ≤ η by norm_num) hX1
  set H := Hcut η X
  have hHR : (H : ℝ) ≤ (X : ℝ) ^ η := hH.1
  have hH1 : (H : ℝ) + 1 ≤ 2 * (X : ℝ) ^ η := hH.2
  have hXη : 0 < (X : ℝ) ^ η := by positivity
  -- small part
  have hsmall := smallSet_card_crude (σ := (1 : ℝ) / 3) (show (0 : ℝ) ≤ η by norm_num) hX1
  have hsqrt : Real.sqrt X + 1 ≤ 2 * (X : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    have : (1 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hX1R (by norm_num)
    linarith
  have hsmall2 : ((smallSet ((1 : ℝ) / 3) η X).card : ℝ) ≤ 16 * (X : ℝ) ^ ((9 : ℝ) / 10) := by
    have e : (X : ℝ) ^ ((9 : ℝ) / 10) ≥ (X : ℝ) ^ η * (X : ℝ) ^ η * (X : ℝ) ^ ((1 : ℝ) / 3) *
        (X : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hX0R, ← Real.rpow_add hX0R, ← Real.rpow_add hX0R]
      exact Real.rpow_le_rpow_of_exponent_le hX1R (by norm_num [η])
    have hX3 : 0 ≤ (X : ℝ) ^ ((1 : ℝ) / 3) := by positivity
    have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
    calc ((smallSet ((1 : ℝ) / 3) η X).card : ℝ)
        ≤ ((H : ℝ) + 1) * (4 * H * (X : ℝ) ^ ((1 : ℝ) / 3)) * (Real.sqrt X + 1) := hsmall
      _ ≤ (2 * (X : ℝ) ^ η) * (4 * (X : ℝ) ^ η * (X : ℝ) ^ ((1 : ℝ) / 3)) *
          (2 * (X : ℝ) ^ ((1 : ℝ) / 2)) := by
          apply mul_le_mul (mul_le_mul hH1 _ (by positivity) (by positivity)) hsqrt
            (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_right _ hX3
          linarith
      _ = 16 * ((X : ℝ) ^ η * (X : ℝ) ^ η * (X : ℝ) ^ ((1 : ℝ) / 3) * (X : ℝ) ^ ((1 : ℝ) / 2)) := by
          ring
      _ ≤ 16 * (X : ℝ) ^ ((9 : ℝ) / 10) := by linarith
  -- large part
  have hlarge : ((∑ ah ∈ largePairs ((1 : ℝ) / 3) η X, (fibre X ah.1 ah.2).card : ℕ) : ℝ) ≤
      4 * max C 0 * (X : ℝ) ^ ((9 : ℝ) / 10) := by
    push_cast
    have hpair : ∀ ah ∈ largePairs ((1 : ℝ) / 3) η X,
        ((fibre X ah.1 ah.2).card : ℝ) ≤ max C 0 * (X : ℝ) ^ ((71 : ℝ) / 100) := by
      intro ah hah
      rw [largePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_Icc] at hah
      obtain ⟨⟨ha, hh2, hhH⟩, hk⟩ := hah
      have := hN₁ X hX1' ah.1 ah.2 (by omega) hh2 hhH hk
      exact le_trans this (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hcard := card_largePairs_le ((1 : ℝ) / 3) η X
    calc ∑ ah ∈ largePairs ((1 : ℝ) / 3) η X, ((fibre X ah.1 ah.2).card : ℝ)
        ≤ ∑ _ah ∈ largePairs ((1 : ℝ) / 3) η X, max C 0 * (X : ℝ) ^ ((71 : ℝ) / 100) :=
          Finset.sum_le_sum hpair
      _ = ((largePairs ((1 : ℝ) / 3) η X).card : ℝ) * (max C 0 * (X : ℝ) ^ ((71 : ℝ) / 100)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((H : ℝ) + 1) * ((H : ℝ) + 1)) * (max C 0 * (X : ℝ) ^ ((71 : ℝ) / 100)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
      _ ≤ (2 * (X : ℝ) ^ η * (2 * (X : ℝ) ^ η)) * (max C 0 * (X : ℝ) ^ ((71 : ℝ) / 100)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul hH1 hH1 (by positivity) (by positivity)
      _ = 4 * max C 0 * ((X : ℝ) ^ η * (X : ℝ) ^ η * (X : ℝ) ^ ((71 : ℝ) / 100)) := by ring
      _ ≤ 4 * max C 0 * (X : ℝ) ^ ((9 : ℝ) / 10) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← Real.rpow_add hX0R, ← Real.rpow_add hX0R]
          exact Real.rpow_le_rpow_of_exponent_le hX1R (by norm_num [η])
  calc (prefixCount ESet X : ℝ)
      ≤ ((smallSet ((1 : ℝ) / 3) η X).card +
          ∑ ah ∈ largePairs ((1 : ℝ) / 3) η X, (fibre X ah.1 ah.2).card : ℕ) := by
        exact_mod_cast hdec
    _ = ((smallSet ((1 : ℝ) / 3) η X).card : ℝ) +
          ((∑ ah ∈ largePairs ((1 : ℝ) / 3) η X, (fibre X ah.1 ah.2).card : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ 16 * (X : ℝ) ^ ((9 : ℝ) / 10) + 4 * max C 0 * (X : ℝ) ^ ((9 : ℝ) / 10) :=
        add_le_add hsmall2 hlarge
    _ = (16 + 4 * max C 0) * (X : ℝ) ^ ((9 : ℝ) / 10) := by ring

end Erdos374.D35

end
