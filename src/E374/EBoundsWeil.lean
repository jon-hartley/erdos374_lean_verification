import E374.EBounds

/-!
# `E(X) ≪ X^{2/5+ε}` (kernel-size balancing, σ = 1/5)

Inputs: RM, factorial growth and the coarse Weil bound (all proved in the project).
The small-kernel Pell fibres are bounded by the elementary class count
`pell_count_le` (`E374.PellClass`); Tao's Lemma 2.10 is not needed.
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

/-- Weil fibre bound: `|T(a,h)| ≤ C X^{2/5+4η}` in the large-kernel regime `q_a > X^{h/5}`. -/
theorem fibre_card_le_weil (hW : CoarseWeilBound) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 100) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ X : ℕ, N ≤ X → ∀ a h : ℕ, a ≤ Hcut η X → 2 ≤ h →
      h ≤ Hcut η X → ((X : ℝ) ^ ((1 : ℝ) / 5)) ^ h < (q a : ℝ) →
      ((fibre X a h).card : ℝ) ≤ C * (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η) := by
  obtain ⟨CM, hCM⟩ := mertens_interval
  set δ : ℝ := η / 4 with hδ
  set c₀ : ℝ := Real.log 4 + 2 * Real.log 2 + 2 * |CM| + 2 * δ * |CM| with hc₀
  obtain ⟨N₁, hN₁⟩ := nat_eventually_log_gt (2 / η * c₀ + 1)
  obtain ⟨N₂, hN₂⟩ := nat_eventually_rpow_gt (show (0 : ℝ) < 2 / 5 + 4 * η by linarith) 2
  -- `√Y ≥ 24 H / η`: from `X^{η/2} ≥ 48/η`
  obtain ⟨N₃, hN₃⟩ := nat_eventually_rpow_gt (show (0 : ℝ) < η / 2 by linarith) (48 / η)
  obtain ⟨N₄, hN₄⟩ := nat_eventually_rpow_gt (show (0 : ℝ) < 3 * η by linarith) 2
  refine ⟨2 * Real.log 4 / η, max (max N₁ N₂) (max (max N₃ N₄) 2),
    fun X hX a h haH hh hhH hk => ?_⟩
  have hXN₁ : N₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXN₂ : N₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXN₃ : N₃ ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hX
  have hXN₄ : N₄ ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hX
  have hX1 : 1 ≤ X := le_trans (by norm_num) (le_trans (le_max_right _ _) (le_trans
    (le_max_right _ _) hX))
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hX0R : (0 : ℝ) < X := by linarith
  have hlogX := hN₁ X hXN₁
  have hQ2 := hN₂ X hXN₂
  have hXη2 := hN₃ X hXN₃
  have hY2 := hN₄ X hXN₄
  set Y : ℕ := ⌊(X : ℝ) ^ (3 * η)⌋₊ with hY
  set Q : ℕ := ⌊(X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η)⌋₊ with hQ
  set H := Hcut η X with hHdef
  have hHle : (H : ℝ) ≤ (X : ℝ) ^ η := (Hcut_le hη.le hX1).1
  have hHY : H ≤ Y := by
    apply Nat.floor_le_floor
    exact Real.rpow_le_rpow_of_exponent_le hX1R (by linarith)
  have hYQ : Y ≤ Q := by
    apply Nat.floor_le_floor
    exact Real.rpow_le_rpow_of_exponent_le hX1R (by linarith)
  have hfb := fibre_bound_weil (Q := Q) hW hX1 hh (by omega : a < Y + 1) (by omega : h < Y + 1)
  have hhR : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hhH' : (h : ℝ) ≤ (X : ℝ) ^ η := le_trans (by exact_mod_cast hhH) hHle
  -- Y is large: `(X^{3η})/2 ≤ Y`, so `√Y ≥ X^{3η/2}/2`
  have hYge : (X : ℝ) ^ (3 * η) / 2 ≤ (Y : ℝ) := by
    have := Nat.lt_floor_add_one ((X : ℝ) ^ (3 * η)); linarith
  -- per-prime comparison of the Weil residue count with `p (1+δ)/2`
  have hρ : ∀ p ∈ auxPrimes Y Q,
      (2 / (1 + δ)) * (Real.log p / p) ≤
        Real.log p / (((p : ℝ) + h + 5 * h * Real.sqrt p) / 2) := by
    intro p hp
    rw [auxPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    have hpY : Y < p := hp.1.1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.one_lt.le
    have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hsp : 1 ≤ Real.sqrt p := by rw [Real.one_le_sqrt]; exact hp1
    -- `6 h ≤ δ √p`
    have h6 : 6 * (h : ℝ) ≤ δ * Real.sqrt p := by
      have hYp : (Y : ℝ) ≤ p := by exact_mod_cast hpY.le
      have hsY : Real.sqrt ((X : ℝ) ^ (3 * η) / 2) ≤ Real.sqrt p :=
        Real.sqrt_le_sqrt (le_trans hYge hYp)
      have hsq : Real.sqrt ((X : ℝ) ^ (3 * η) / 2) ≥ (X : ℝ) ^ (3 * η / 2) / 2 := by
        rw [ge_iff_le, Real.le_sqrt (by positivity) (by positivity)]
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hX0R.le]
        have : (X : ℝ) ^ (3 * η / 2 * ((2 : ℕ) : ℝ)) = (X : ℝ) ^ (3 * η) := by
          congr 1; push_cast; ring
        rw [this]
        have : (1 : ℝ) ≤ (X : ℝ) ^ (3 * η) := Real.one_le_rpow hX1R (by linarith)
        linarith
      have hsplit : (X : ℝ) ^ (3 * η / 2) = (X : ℝ) ^ η * (X : ℝ) ^ (η / 2) := by
        rw [← Real.rpow_add hX0R]; ring_nf
      have hXη0 : 0 < (X : ℝ) ^ η := by positivity
      calc 6 * (h : ℝ) ≤ 6 * (X : ℝ) ^ η := by linarith
        _ = δ * ((X : ℝ) ^ η * (48 / η)) / 2 := by rw [hδ]; field_simp; ring
        _ ≤ δ * ((X : ℝ) ^ η * (X : ℝ) ^ (η / 2)) / 2 := by
            have : 0 < δ := by rw [hδ]; positivity
            gcongr
        _ = δ * ((X : ℝ) ^ (3 * η / 2) / 2) := by rw [hsplit]; ring
        _ ≤ δ * Real.sqrt p := by
            have : 0 < δ := by rw [hδ]; positivity
            gcongr
            linarith
    have hden : ((p : ℝ) + h + 5 * h * Real.sqrt p) / 2 ≤ (p : ℝ) * (1 + δ) / 2 := by
      have h1 : (h : ℝ) ≤ h * Real.sqrt p := by nlinarith
      have h2 : 6 * (h : ℝ) * Real.sqrt p ≤ δ * Real.sqrt p * Real.sqrt p := by nlinarith
      have h3 : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
      nlinarith
    have hpos : 0 < ((p : ℝ) + h + 5 * h * Real.sqrt p) / 2 := by positivity
    have hδ0 : 0 < 1 + δ := by rw [hδ]; positivity
    calc (2 / (1 + δ)) * (Real.log p / p) = Real.log p / ((p : ℝ) * (1 + δ) / 2) := by
          field_simp
      _ ≤ _ := div_le_div_of_nonneg_left hlp hpos hden
  have hsumρ : (2 / (1 + δ)) * (Real.log Q - Real.log Y - CM) ≤
      ∑ p ∈ auxPrimes Y Q, Real.log p / (((p : ℝ) + h + 5 * h * Real.sqrt p) / 2) := by
    have hδ0 : 0 < 1 + δ := by rw [hδ]; positivity
    calc (2 / (1 + δ)) * (Real.log Q - Real.log Y - CM)
        ≤ (2 / (1 + δ)) * ∑ p ∈ auxPrimes Y Q, Real.log p / p :=
          mul_le_mul_of_nonneg_left (hCM Y Q hYQ) (by positivity)
      _ = ∑ p ∈ auxPrimes Y Q, (2 / (1 + δ)) * (Real.log p / p) := by rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum hρ
  -- logarithms of Q and Y
  have hlogQ : Real.log ((X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η)) - Real.log 2 ≤ Real.log Q :=
    log_floor_ge hQ2.le
  rw [log_rpow_nat hX1] at hlogQ
  have hlogQ' : Real.log Q ≤ ((2 : ℝ) / 5 + 4 * η) * Real.log X := by
    have h1 : (1 : ℝ) ≤ (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η) := Real.one_le_rpow hX1R (by linarith)
    have := log_floor_le h1
    rwa [log_rpow_nat hX1] at this
  have hlogY : Real.log Y ≤ 3 * η * Real.log X := by
    have h1 : (1 : ℝ) ≤ (X : ℝ) ^ (3 * η) := Real.one_le_rpow hX1R (by linarith)
    have := log_floor_le h1
    rwa [log_rpow_nat hX1] at this
  have hlogY0 : 0 ≤ Real.log Y := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ Y := by
      have := Nat.le_floor (show ((2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (3 * η) by push_cast; linarith)
      exact_mod_cast this
    linarith
  have hlX0 : 0 ≤ Real.log X := Real.log_nonneg hX1R
  have hlogq := log_q_div_gt hX1 (by omega) hk
  have hsplit : (Real.log (q a) - Real.log 4 * h) / h = Real.log (q a) / h - Real.log 4 := by
    field_simp
  set L := Real.log Q - Real.log Y - CM with hL
  have hLlow : (2 / 5 + η) * Real.log X - Real.log 2 - CM ≤ L := by rw [hL]; nlinarith
  have hLup : L ≤ Real.log X + |CM| := by
    rw [hL]
    have : ((2 : ℝ) / 5 + 4 * η) * Real.log X ≤ Real.log X := by nlinarith
    have := neg_abs_le CM
    linarith
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hfac : (2 - 2 * δ) * L ≤ (2 / (1 + δ)) * L ∨ L < 0 := by
    by_cases hL0 : 0 ≤ L
    · left
      apply mul_le_mul_of_nonneg_right _ hL0
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    · right; linarith
  have hlogbig : c₀ * 2 / η < Real.log X := by
    have : 2 / η * c₀ = c₀ * 2 / η := by ring
    linarith
  have hc₀pos : 0 ≤ c₀ := by
    rw [hc₀]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    have : 0 ≤ δ := by rw [hδ]; positivity
    positivity
  have hLpos : 0 ≤ L := by
    have : c₀ * 2 / η ≥ 0 := by positivity
    have h2 : Real.log 2 + CM ≤ c₀ := by
      rw [hc₀]
      have := le_abs_self CM
      have := abs_nonneg CM
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ0) (abs_nonneg CM)
      linarith
    have : c₀ ≤ (2 / 5 + η) * Real.log X := by
      have : c₀ * 2 / η ≤ Real.log X := hlogbig.le
      rw [div_le_iff₀ hη] at this
      nlinarith
    linarith
  have hfac' : (2 - 2 * δ) * L ≤ (2 / (1 + δ)) * L := by
    rcases hfac with h | h
    · exact h
    · linarith
  have hD : η * Real.log X ≤
      (Real.log (q a) - Real.log 4 * h) / h +
        ∑ p ∈ auxPrimes Y Q, Real.log p / (((p : ℝ) + h + 5 * h * Real.sqrt p) / 2) -
        Real.log X := by
    rw [hsplit]
    have hA : (2 - 2 * δ) * L ≥ 2 * ((2 / 5 + η) * Real.log X - Real.log 2 - CM) -
        2 * δ * (Real.log X + |CM|) := by nlinarith
    have hB : η * Real.log X ≥ c₀ * 2 := by
      have : c₀ * 2 / η ≤ Real.log X := hlogbig.le
      rw [div_le_iff₀ hη] at this; linarith
    have habs := le_abs_self CM
    rw [hc₀] at hB
    have : δ * Real.log X = η / 4 * Real.log X := by rw [hδ]
    nlinarith
  have hRHS : max (Real.log 4 * a + Real.log 4 * Q - Real.log X) 0 ≤
      2 * Real.log 4 * (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η) := by
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have haR : (a : ℝ) ≤ (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η) := by
      have : (a : ℝ) ≤ (X : ℝ) ^ η := le_trans (by exact_mod_cast haH) hHle
      exact le_trans this (Real.rpow_le_rpow_of_exponent_le hX1R (by linarith))
    have hQR : (Q : ℝ) ≤ (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η) := Nat.floor_le (by positivity)
    apply max_le
    · nlinarith
    · positivity
  have hlogX1 : 1 ≤ Real.log X := by
    have : 0 ≤ 2 / η * c₀ := by positivity
    linarith
  have hJ : (0 : ℝ) ≤ (fibre X a h).card := Nat.cast_nonneg _
  have hmain : ((fibre X a h).card : ℝ) * (η * Real.log X) ≤
      2 * Real.log 4 * (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η) :=
    le_trans (mul_le_mul_of_nonneg_left hD hJ) (le_trans hfb hRHS)
  have hpos : 0 < η * Real.log X := by positivity
  have h1 : ((fibre X a h).card : ℝ) ≤
      2 * Real.log 4 * (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η) / (η * Real.log X) :=
    (le_div_iff₀ hpos).mpr hmain
  calc ((fibre X a h).card : ℝ)
      ≤ 2 * Real.log 4 * (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η) / (η * Real.log X) := h1
    _ ≤ 2 * Real.log 4 * (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η) / (η * 1) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hlogX1 hη.le
    _ = 2 * Real.log 4 / η * (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η) := by ring

/-- **`E(X) ≪ X^{2/5+ε}`.** -/
theorem ESet_count_le (hRM : Tasks.ValuationOneMass) (hG : Tasks.FactorialClassGrowth)
    (hW : CoarseWeilBound) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      (prefixCount ESet X : ℝ) ≤ C * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
  intro ε hε
  set η : ℝ := min (ε / 9) (1 / 100) with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  have hη1 : η ≤ 1 / 100 := min_le_right _ _
  have hηε : 9 * η ≤ ε := by have := min_le_left (ε / 9) (1 / 100); rw [← hηdef] at this; linarith
  obtain ⟨N₀, hN₀⟩ := prefixCount_ESet_le hRM hG hη (by linarith) ((1 : ℝ) / 5)
  obtain ⟨CS, NS, hNS⟩ := smallSet_card_pell (σ := (1 : ℝ) / 5) (η := η) (ε := 3 * η)
    (by norm_num) (by norm_num) hη.le (by linarith) (by linarith) le_rfl
  obtain ⟨CL, NL, hNL⟩ := fibre_card_le_weil hW hη hη1
  obtain ⟨N₃, hN₃⟩ := nat_eventually_log_gt 4
  refine ⟨400 * max CS 0 / η + 4 * max CL 0, max (max N₀ NS) (max NL N₃), fun X hX => ?_⟩
  have hXN₀ : N₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXNS : NS ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXNL : NL ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXN₃ : N₃ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hlog4 := hN₃ X hXN₃
  have hX1 : 1 ≤ X := by
    by_contra h0; push_neg at h0
    have : X = 0 := by omega
    rw [this] at hlog4; simp at hlog4; linarith
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hX0R : (0 : ℝ) < X := by linarith
  have hdec := hN₀ X hXN₀
  set H := Hcut η X
  have hH := Hcut_le hη.le hX1
  have hH1 : (H : ℝ) + 1 ≤ 2 * (X : ℝ) ^ η := hH.2
  have hHle : (H : ℝ) ≤ (X : ℝ) ^ η := hH.1
  have hXη0 : 0 < (X : ℝ) ^ η := by positivity
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1R
  -- small part
  have hsmall := hNS X hXNS
  set M := Mcut ((1 : ℝ) / 5) η X with hM
  have hMle : (M : ℝ) ≤ 16 * (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) := by
    have h1 : (M : ℝ) ≤ 16 * (H : ℝ) ^ 2 * ((X : ℝ) ^ ((1 : ℝ) / 5)) ^ 2 :=
      Nat.floor_le (by positivity)
    have h2 : (H : ℝ) ^ 2 * ((X : ℝ) ^ ((1 : ℝ) / 5)) ^ 2 ≤ (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) := by
      have e : (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) =
          ((X : ℝ) ^ η) ^ 2 * ((X : ℝ) ^ ((1 : ℝ) / 5)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hX0R.le,
          ← Real.rpow_mul hX0R.le, ← Real.rpow_add hX0R]
        congr 1; push_cast; ring
      rw [e]
      gcongr
    linarith
  have hMlog : (M : ℝ) * (1 + Real.log M) ≤ 96 * (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) * Real.log X := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · rw [h0]; simp; positivity
    · have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast h0
      have hlogM : Real.log M ≤ Real.log 16 + Real.log X := by
        have hX2 : (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) ≤ X := by
          calc (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) ≤ (X : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hX1R (by linarith)
            _ = X := Real.rpow_one _
        have := Real.log_le_log (by linarith) (le_trans hMle (by nlinarith : 16 * (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) ≤ 16 * X))
        rwa [Real.log_mul (by norm_num) (by linarith)] at this
      have hl16 : Real.log 16 ≤ 4 := by
        have : Real.log 16 = 4 * Real.log 2 := by
          rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      have h1 : 1 + Real.log M ≤ 6 * Real.log X := by linarith
      have hM0 : (0 : ℝ) ≤ M := by linarith
      calc (M : ℝ) * (1 + Real.log M) ≤ (16 * (X : ℝ) ^ (2 * η + (2 : ℝ) / 5)) * (6 * Real.log X) :=
            mul_le_mul hMle h1 (by linarith [Real.log_nonneg hM1]) (by positivity)
        _ = 96 * (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) * Real.log X := by ring
  have hlogle : Real.log X ≤ (X : ℝ) ^ η / η := Real.log_le_rpow_div hX0R.le hη
  have hsmall2 : ((smallSet ((1 : ℝ) / 5) η X).card : ℝ) ≤
      400 * max CS 0 / η * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
    have hCS : CS ≤ max CS 0 := le_max_left _ _
    calc ((smallSet ((1 : ℝ) / 5) η X).card : ℝ)
        ≤ CS * ((H : ℝ) + 1) ^ 2 * ((M : ℝ) * (1 + Real.log M)) * (X : ℝ) ^ (3 * η) := hsmall
      _ ≤ max CS 0 * (2 * (X : ℝ) ^ η) ^ 2 * (96 * (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) *
            ((X : ℝ) ^ η / η)) * (X : ℝ) ^ (3 * η) := by
          have hMl0 : 0 ≤ (M : ℝ) * (1 + Real.log M) := by
            rcases Nat.eq_zero_or_pos M with h0 | h0
            · rw [h0]; simp
            · have : (1 : ℝ) ≤ M := by exact_mod_cast h0
              have := Real.log_nonneg this; positivity
          have hA : (M : ℝ) * (1 + Real.log M) ≤
              96 * (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) * ((X : ℝ) ^ η / η) :=
            le_trans hMlog (mul_le_mul_of_nonneg_left hlogle (by positivity))
          have hH2 : ((H : ℝ) + 1) ^ 2 ≤ (2 * (X : ℝ) ^ η) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hH1 2
          have e1 : CS * ((H : ℝ) + 1) ^ 2 * ((M : ℝ) * (1 + Real.log M)) * (X : ℝ) ^ (3 * η) =
              CS * (((H : ℝ) + 1) ^ 2 * ((M : ℝ) * (1 + Real.log M)) * (X : ℝ) ^ (3 * η)) := by ring
          have e2 : max CS 0 * (2 * (X : ℝ) ^ η) ^ 2 * (96 * (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) *
              ((X : ℝ) ^ η / η)) * (X : ℝ) ^ (3 * η) = max CS 0 * ((2 * (X : ℝ) ^ η) ^ 2 *
              (96 * (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) * ((X : ℝ) ^ η / η)) * (X : ℝ) ^ (3 * η)) := by ring
          rw [e1, e2]
          apply mul_le_mul hCS _ (by positivity) (le_max_right _ _)
          exact mul_le_mul (mul_le_mul hH2 hA hMl0 (by positivity)) le_rfl (by positivity)
            (by positivity)
      _ = 384 * max CS 0 / η * ((X : ℝ) ^ η * (X : ℝ) ^ η * (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) *
            (X : ℝ) ^ η * (X : ℝ) ^ (3 * η)) := by ring
      _ ≤ 400 * max CS 0 / η * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
          have e : (X : ℝ) ^ η * (X : ℝ) ^ η * (X : ℝ) ^ (2 * η + (2 : ℝ) / 5) *
              (X : ℝ) ^ η * (X : ℝ) ^ (3 * η) = (X : ℝ) ^ ((2 : ℝ) / 5 + 8 * η) := by
            rw [← Real.rpow_add hX0R, ← Real.rpow_add hX0R, ← Real.rpow_add hX0R,
              ← Real.rpow_add hX0R]; ring_nf
          rw [e]
          have h6 : (X : ℝ) ^ ((2 : ℝ) / 5 + 8 * η) ≤ (X : ℝ) ^ ((2 : ℝ) / 5 + ε) :=
            Real.rpow_le_rpow_of_exponent_le hX1R (by linarith)
          have ha : 0 ≤ max CS 0 / η := by positivity
          have hY0 : 0 ≤ (X : ℝ) ^ ((2 : ℝ) / 5 + ε) := by positivity
          have e3 : 384 * max CS 0 / η = 384 * (max CS 0 / η) := by ring
          have e4 : 400 * max CS 0 / η = 400 * (max CS 0 / η) := by ring
          rw [e3, e4]
          calc 384 * (max CS 0 / η) * (X : ℝ) ^ ((2 : ℝ) / 5 + 8 * η)
              ≤ 384 * (max CS 0 / η) * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) :=
                mul_le_mul_of_nonneg_left h6 (by positivity)
            _ ≤ 400 * (max CS 0 / η) * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
                have := mul_nonneg ha hY0
                nlinarith
  -- large part
  have hlarge : ((∑ ah ∈ largePairs ((1 : ℝ) / 5) η X, (fibre X ah.1 ah.2).card : ℕ) : ℝ) ≤
      4 * max CL 0 * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
    push_cast
    have hpair : ∀ ah ∈ largePairs ((1 : ℝ) / 5) η X,
        ((fibre X ah.1 ah.2).card : ℝ) ≤ max CL 0 * (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η) := by
      intro ah hah
      rw [largePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_Icc] at hah
      obtain ⟨⟨ha, hh2, hhH⟩, hk⟩ := hah
      have := hNL X hXNL ah.1 ah.2 (by omega) hh2 hhH hk
      exact le_trans this (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hcard := card_largePairs_le ((1 : ℝ) / 5) η X
    calc ∑ ah ∈ largePairs ((1 : ℝ) / 5) η X, ((fibre X ah.1 ah.2).card : ℝ)
        ≤ ∑ _ah ∈ largePairs ((1 : ℝ) / 5) η X, max CL 0 * (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η) :=
          Finset.sum_le_sum hpair
      _ = ((largePairs ((1 : ℝ) / 5) η X).card : ℝ) *
            (max CL 0 * (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((H : ℝ) + 1) * ((H : ℝ) + 1)) * (max CL 0 * (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
      _ ≤ (2 * (X : ℝ) ^ η * (2 * (X : ℝ) ^ η)) * (max CL 0 * (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul hH1 hH1 (by positivity) (by positivity)
      _ = 4 * max CL 0 * ((X : ℝ) ^ η * (X : ℝ) ^ η * (X : ℝ) ^ ((2 : ℝ) / 5 + 4 * η)) := by ring
      _ ≤ 4 * max CL 0 * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← Real.rpow_add hX0R, ← Real.rpow_add hX0R]
          exact Real.rpow_le_rpow_of_exponent_le hX1R (by linarith)
  calc (prefixCount ESet X : ℝ)
      ≤ ((smallSet ((1 : ℝ) / 5) η X).card +
          ∑ ah ∈ largePairs ((1 : ℝ) / 5) η X, (fibre X ah.1 ah.2).card : ℕ) := by
        exact_mod_cast hdec
    _ = ((smallSet ((1 : ℝ) / 5) η X).card : ℝ) +
          ((∑ ah ∈ largePairs ((1 : ℝ) / 5) η X, (fibre X ah.1 ah.2).card : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ 400 * max CS 0 / η * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) +
          4 * max CL 0 * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) := add_le_add hsmall2 hlarge
    _ = (400 * max CS 0 / η + 4 * max CL 0) * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) := by ring

end Erdos374.D35

end
