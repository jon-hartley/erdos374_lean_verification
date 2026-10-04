import E374.ESet
import E374.Inputs
import E374.PellClass
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Small-kernel endpoints

Two bounds for `smallSet σ η X` (configurations with `q_a ≤ (X^σ)^h`):

* `smallSet_card_crude` (no analytic input): the smallest block kernel is `≤ 4 h X^σ`,
  so `|smallSet| ≤ (H+1) · 4 H X^σ · (√X + 1)`.
* `smallSet_card_pell`: the two smallest kernels have product `≤ 16 h² X^{2σ}` and satisfy
  `e₁u² − e₂v² = d` with `1 ≤ d ≤ H`; each such fibre has `≤ d² (log₂(2√e₁X) + 1)`
  elements by the elementary class count `pell_count_le` (no Tao/Pell input).
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

/-- Real form of the kernel product bound under the small-kernel hypothesis. -/
theorem kernel_prod_le_real {a h m X : ℕ} {σ : ℝ} (hhm : h ≤ m)
    (hs : IsSquare (q a * falling h m)) (hk : (q a : ℝ) ≤ ((X : ℝ) ^ σ) ^ h) :
    ((∏ i ∈ Finset.range h, sf (m - i) : ℕ) : ℝ) ≤ (4 * h * (X : ℝ) ^ σ) ^ h := by
  have h1 := kernel_prod_le hhm hs
  have h2 : ((∏ i ∈ Finset.range h, sf (m - i) : ℕ) : ℝ) ≤ (q a : ℝ) * ((h : ℝ) ^ h * 4 ^ h) := by
    exact_mod_cast h1
  have hX0 : (0 : ℝ) ≤ ((h : ℝ) ^ h * 4 ^ h) := by positivity
  calc _ ≤ (q a : ℝ) * ((h : ℝ) ^ h * 4 ^ h) := h2
    _ ≤ ((X : ℝ) ^ σ) ^ h * ((h : ℝ) ^ h * 4 ^ h) := mul_le_mul_of_nonneg_right hk hX0
    _ = (4 * h * (X : ℝ) ^ σ) ^ h := by ring

/-- **Crude small-kernel bound.** -/
theorem smallSet_card_crude {σ η : ℝ} (hη : 0 ≤ η) {X : ℕ} (hX : 1 ≤ X) :
    ((smallSet σ η X).card : ℝ) ≤
      ((Hcut η X : ℝ) + 1) * (4 * Hcut η X * (X : ℝ) ^ σ) * (Real.sqrt X + 1) := by
  classical
  set H := Hcut η X with hH
  set D : ℕ := ⌊4 * (H : ℝ) * (X : ℝ) ^ σ⌋₊ with hD
  have hsub : smallSet σ η X ⊆
      ((Finset.range (H + 1)) ×ˢ (Finset.Icc 1 D) ×ˢ (Finset.range (Nat.sqrt X + 1))).image
        (fun t : ℕ × ℕ × ℕ => t.2.1 * t.2.2 ^ 2 + t.1) := by
    intro m hm
    rw [smallSet, Finset.mem_filter] at hm
    obtain ⟨hmI, a, h, haH, hh, hhH, hahm, hs, hk⟩ := hm
    have hmX : m ≤ X := (Finset.mem_Icc.mp hmI).2
    have hhm : h ≤ m := by omega
    have hne : (Finset.range h).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
    obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image (Finset.range h) (fun i => sf (m - i)) hne
    have hi0h : i0 < h := Finset.mem_range.mp hi0
    set d0 := sf (m - i0) with hd0
    have hpow : d0 ^ h ≤ ∏ i ∈ Finset.range h, sf (m - i) := by
      have := Finset.pow_card_le_prod (Finset.range h) (fun i => sf (m - i)) d0 hmin
      rwa [Finset.card_range] at this
    have hreal : (d0 : ℝ) ^ h ≤ (4 * h * (X : ℝ) ^ σ) ^ h := by
      have := kernel_prod_le_real hhm hs hk
      calc (d0 : ℝ) ^ h = ((d0 ^ h : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ ((∏ i ∈ Finset.range h, sf (m - i) : ℕ) : ℝ) := by exact_mod_cast hpow
        _ ≤ _ := this
    have hX0 : (0 : ℝ) ≤ (X : ℝ) ^ σ := by positivity
    have hd0le : (d0 : ℝ) ≤ 4 * h * (X : ℝ) ^ σ :=
      le_of_pow_le_pow_left₀ (by omega) (by positivity) hreal
    have hd0D : d0 ≤ D := by
      apply Nat.le_floor
      calc (d0 : ℝ) ≤ 4 * h * (X : ℝ) ^ σ := hd0le
        _ ≤ 4 * H * (X : ℝ) ^ σ := by
          have : (h : ℝ) ≤ H := by exact_mod_cast hhH
          nlinarith
    have hd0pos : 1 ≤ d0 := sf_pos _
    obtain ⟨u, hu⟩ := sf_mul_sq (show m - i0 ≠ 0 by omega)
    rw [← hd0] at hu
    have hu2 : u ^ 2 ≤ X := by
      have : u ^ 2 ≤ d0 * u ^ 2 := Nat.le_mul_of_pos_left _ hd0pos
      omega
    rw [Finset.mem_image]
    refine ⟨(i0, d0, u), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
      exact ⟨by omega, ⟨hd0pos, hd0D⟩, Nat.lt_succ_of_le (Nat.le_sqrt'.mpr hu2)⟩
    · simp only
      omega
  have hcard := Finset.card_le_card hsub
  have hcard2 := le_trans hcard Finset.card_image_le
  rw [Finset.card_product, Finset.card_product, Finset.card_range, Nat.card_Icc,
    Finset.card_range] at hcard2
  have hDle : (D : ℝ) ≤ 4 * (H : ℝ) * (X : ℝ) ^ σ := Nat.floor_le (by positivity)
  have hsq : (Nat.sqrt X : ℝ) ≤ Real.sqrt X := Real.nat_sqrt_le_real_sqrt
  calc ((smallSet σ η X).card : ℝ) ≤ ((H + 1) * ((D + 1 - 1) * (Nat.sqrt X + 1)) : ℕ) := by
        exact_mod_cast hcard2
    _ = ((H : ℝ) + 1) * (D : ℝ) * ((Nat.sqrt X : ℝ) + 1) := by
        rw [Nat.add_sub_cancel]; push_cast; ring
    _ ≤ ((H : ℝ) + 1) * (4 * H * (X : ℝ) ^ σ) * (Real.sqrt X + 1) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hDle (by positivity)
        · linarith
        · positivity
        · positivity

/-- Real harmonic bound. -/
theorem sum_inv_Icc_le (n : ℕ) : ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  exact h

/-- `#{(e₁,e₂) ∈ [1,M]² : e₁ e₂ ≤ M} ≤ M (1 + log M)`. -/
theorem card_pairs_le (M : ℕ) :
    ((((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter (fun e : ℕ × ℕ => e.1 * e.2 ≤ M)).card : ℝ)
      ≤ M * (1 + Real.log M) := by
  classical
  have hsub : ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter (fun e : ℕ × ℕ => e.1 * e.2 ≤ M) ⊆
      (Finset.Icc 1 M).biUnion (fun e1 => ({e1} : Finset ℕ) ×ˢ Finset.Icc 1 (M / e1)) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at he
    rw [Finset.mem_biUnion]
    refine ⟨e.1, Finset.mem_Icc.mpr he.1.1, ?_⟩
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_Icc]
    refine ⟨by simp, he.1.2.1, ?_⟩
    rw [Nat.le_div_iff_mul_le (by omega)]
    rw [mul_comm]; exact he.2
  have h1 := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  simp only [Finset.card_product, Finset.card_singleton, Nat.card_Icc, one_mul,
    Nat.add_sub_cancel] at h1
  have h2 : ((∑ e1 ∈ Finset.Icc 1 M, M / e1 : ℕ) : ℝ) ≤ ∑ e1 ∈ Finset.Icc 1 M, (M : ℝ) * (e1 : ℝ)⁻¹ := by
    push_cast
    apply Finset.sum_le_sum
    intro e1 he1
    have hpos : (0 : ℝ) < e1 := by exact_mod_cast (Finset.mem_Icc.mp he1).1
    rw [← div_eq_mul_inv]
    exact Nat.cast_div_le
  calc _ ≤ ((∑ e1 ∈ Finset.Icc 1 M, M / e1 : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ ∑ e1 ∈ Finset.Icc 1 M, (M : ℝ) * (e1 : ℝ)⁻¹ := h2
    _ = (M : ℝ) * ∑ e1 ∈ Finset.Icc 1 M, (e1 : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ M * (1 + Real.log M) :=
        mul_le_mul_of_nonneg_left (sum_inv_Icc_le M) (Nat.cast_nonneg M)

open Classical in
/-- Pell solution set used in the small-kernel count. -/
def pellSol (X e1 e2 : ℕ) (Δ : ℤ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun u : ℕ => ∃ v : ℕ, (e1 : ℤ) * (u : ℤ) ^ 2 + Δ = (e2 : ℤ) * (v : ℤ) ^ 2)

/-- The coefficient bound `M = ⌊16 H² X^{2σ}⌋`. -/
def Mcut (σ η : ℝ) (X : ℕ) : ℕ := ⌊16 * (Hcut η X : ℝ) ^ 2 * ((X : ℝ) ^ σ) ^ 2⌋₊

open Classical in
/-- **Small-kernel bound.** Each Pell fibre is bounded by the elementary class count
`pell_count_le` (`d² (log₂(2√e₁X) + 1)` with `d ≤ H = ⌊X^η⌋`), which is `≪ X^ε` once
`3η ≤ ε`. No input beyond elementary number theory is used (Tao's Lemma 2.10 is not
needed). -/
theorem smallSet_card_pell {σ η ε : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2)
    (hη : 0 ≤ η) (hη1 : η ≤ 1 / 2) (hε : 0 < ε) (hηε : 3 * η ≤ ε) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      ((smallSet σ η X).card : ℝ) ≤
        C * ((Hcut η X : ℝ) + 1) ^ 2 * ((Mcut σ η X : ℝ) * (1 + Real.log (Mcut σ η X))) *
          (X : ℝ) ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := 15 / (ε * Real.log 2) + 1 with hCdef
  have hC0 : 0 < C := by rw [hCdef]; positivity
  refine ⟨max C 0, 16, fun X hX => ?_⟩
  have hX16 : 16 ≤ X := hX
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hX0R : (0 : ℝ) < X := by linarith
  set H := Hcut η X with hH
  set M := Mcut σ η X with hM
  set I : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (((Finset.range (H + 1)) ×ˢ (Finset.range (H + 1))).filter (fun ij => ij.1 < ij.2)) ×ˢ
      (((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter (fun e : ℕ × ℕ => e.1 * e.2 ≤ M)) with hI
  have hsub : smallSet σ η X ⊆ I.biUnion (fun t =>
      (pellSol X t.2.1 t.2.2 ((t.1.1 : ℤ) - t.1.2)).image (fun u => t.2.1 * u ^ 2 + t.1.1)) := by
    intro m hm
    rw [smallSet, Finset.mem_filter] at hm
    obtain ⟨hmI, a, h, haH, hh, hhH, hahm, hs, hk⟩ := hm
    have hmX : m ≤ X := (Finset.mem_Icc.mp hmI).2
    have hhm : h ≤ m := by omega
    obtain ⟨i, j, hij, hjh, hpow⟩ := exists_two_small (fun k => sf (m - k)) hh
    set e1 := sf (m - i) with he1
    set e2 := sf (m - j) with he2
    have hreal : ((e1 * e2 : ℕ) : ℝ) ^ h ≤ (16 * (h : ℝ) ^ 2 * ((X : ℝ) ^ σ) ^ 2) ^ h := by
      have hk2 := kernel_prod_le_real hhm hs hk
      have hP0 : (0 : ℝ) ≤ ((∏ k ∈ Finset.range h, sf (m - k) : ℕ) : ℝ) := Nat.cast_nonneg _
      calc ((e1 * e2 : ℕ) : ℝ) ^ h = (((e1 * e2) ^ h : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ (((∏ k ∈ Finset.range h, sf (m - k)) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hpow
        _ = ((∏ k ∈ Finset.range h, sf (m - k) : ℕ) : ℝ) ^ 2 := by push_cast; rfl
        _ ≤ ((4 * h * (X : ℝ) ^ σ) ^ h) ^ 2 := pow_le_pow_left₀ hP0 hk2 2
        _ = (16 * (h : ℝ) ^ 2 * ((X : ℝ) ^ σ) ^ 2) ^ h := by
            rw [← pow_mul, mul_comm h 2, pow_mul]; congr 1; ring
    have hprod : ((e1 * e2 : ℕ) : ℝ) ≤ 16 * (h : ℝ) ^ 2 * ((X : ℝ) ^ σ) ^ 2 :=
      le_of_pow_le_pow_left₀ (by omega) (by positivity) hreal
    have hprodM : e1 * e2 ≤ M := by
      apply Nat.le_floor
      have hhH' : (h : ℝ) ≤ H := by exact_mod_cast hhH
      have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
      calc ((e1 * e2 : ℕ) : ℝ) ≤ 16 * (h : ℝ) ^ 2 * ((X : ℝ) ^ σ) ^ 2 := hprod
        _ ≤ 16 * (H : ℝ) ^ 2 * ((X : ℝ) ^ σ) ^ 2 := by
          have : (h : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 := pow_le_pow_left₀ hh0 hhH' 2
          have : (0 : ℝ) ≤ ((X : ℝ) ^ σ) ^ 2 := by positivity
          nlinarith
    have he1pos : 1 ≤ e1 := sf_pos _
    have he2pos : 1 ≤ e2 := sf_pos _
    have he1M : e1 ≤ M := le_trans (Nat.le_mul_of_pos_right _ he2pos) hprodM
    have he2M : e2 ≤ M := le_trans (Nat.le_mul_of_pos_left _ he1pos) hprodM
    obtain ⟨u, hu⟩ := sf_mul_sq (show m - i ≠ 0 by omega)
    obtain ⟨v, hv⟩ := sf_mul_sq (show m - j ≠ 0 by omega)
    rw [← he1] at hu
    rw [← he2] at hv
    have hu0 : 1 ≤ u := by
      rcases Nat.eq_zero_or_pos u with h0 | h0
      · rw [h0] at hu; simp at hu; omega
      · exact h0
    have huX : u ≤ X := by
      have h1 : u ≤ u ^ 2 := by nlinarith
      have h2 : u ^ 2 ≤ e1 * u ^ 2 := Nat.le_mul_of_pos_left _ he1pos
      omega
    rw [Finset.mem_biUnion]
    refine ⟨((i, j), (e1, e2)), ?_, ?_⟩
    · rw [hI]
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      exact ⟨⟨⟨by omega, by omega⟩, hij⟩, ⟨⟨he1pos, he1M⟩, ⟨he2pos, he2M⟩⟩, hprodM⟩
    · rw [Finset.mem_image]
      refine ⟨u, ?_, by simp only; omega⟩
      rw [pellSol, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hu0, huX⟩, v, ?_⟩
      have h1 : ((m - i : ℕ) : ℤ) = (m : ℤ) - i := Nat.cast_sub (by omega)
      have h2 : ((m - j : ℕ) : ℤ) = (m : ℤ) - j := Nat.cast_sub (by omega)
      have h3 : ((m - i : ℕ) : ℤ) = (e1 : ℤ) * (u : ℤ) ^ 2 := by rw [hu]; push_cast; ring
      have h4 : ((m - j : ℕ) : ℤ) = (e2 : ℤ) * (v : ℤ) ^ 2 := by rw [hv]; push_cast; ring
      linarith
  -- each Pell fibre is small
  have hfib : ∀ t ∈ I, ((pellSol X t.2.1 t.2.2 ((t.1.1 : ℤ) - t.1.2)).card : ℝ) ≤ C * (X : ℝ) ^ ε := by
    intro t ht
    rw [hI] at ht
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at ht
    obtain ⟨⟨⟨hi, hj⟩, hij⟩, ⟨⟨h1, h1M⟩, ⟨h2, h2M⟩⟩, _⟩ := ht
    have hMle : (M : ℝ) ≤ (X : ℝ) ^ (3 : ℝ) := by
      have hHle := (Hcut_le hη (show 1 ≤ X by omega)).1
      have hMf : (M : ℝ) ≤ 16 * (H : ℝ) ^ 2 * ((X : ℝ) ^ σ) ^ 2 := Nat.floor_le (by positivity)
      have hXη : (X : ℝ) ^ η ≤ (X : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hX1R hη1
      have hXσ : (X : ℝ) ^ σ ≤ (X : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hX1R hσ1
      have hsq : ((X : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = X := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0R.le]; norm_num
      have hX3 : (X : ℝ) ^ (3 : ℝ) = X * X * X := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
      have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
      have hA : (H : ℝ) ^ 2 ≤ X := by
        calc (H : ℝ) ^ 2 ≤ ((X : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 :=
              pow_le_pow_left₀ hH0 (le_trans hHle hXη) 2
          _ = X := hsq
      have hB : ((X : ℝ) ^ σ) ^ 2 ≤ X := by
        calc ((X : ℝ) ^ σ) ^ 2 ≤ ((X : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 :=
              pow_le_pow_left₀ (by positivity) hXσ 2
          _ = X := hsq
      have h16 : (16 : ℝ) ≤ X := by exact_mod_cast hX16
      rw [hX3]
      calc (M : ℝ) ≤ 16 * (H : ℝ) ^ 2 * ((X : ℝ) ^ σ) ^ 2 := hMf
        _ ≤ X * X * X := by
          have : (0 : ℝ) ≤ ((X : ℝ) ^ σ) ^ 2 := by positivity
          have : (0 : ℝ) ≤ (H : ℝ) ^ 2 := by positivity
          calc 16 * (H : ℝ) ^ 2 * ((X : ℝ) ^ σ) ^ 2 ≤ (X : ℝ) * (H : ℝ) ^ 2 * ((X : ℝ) ^ σ) ^ 2 := by
                gcongr
            _ ≤ (X : ℝ) * (X : ℝ) * (X : ℝ) := by gcongr
    -- rewrite the fibre in the form of `pell_count_le`
    set d := t.1.2 - t.1.1 with hd
    have hd1 : 1 ≤ d := by omega
    have hdH : d ≤ H := by omega
    have heq : pellSol X t.2.1 t.2.2 ((t.1.1 : ℤ) - t.1.2) = (Finset.Icc 1 X).filter
        (fun u : ℕ => ∃ v : ℕ, (t.2.1 : ℤ) * (u : ℤ) ^ 2 - d = t.2.2 * (v : ℤ) ^ 2) := by
      unfold pellSol
      apply Finset.filter_congr
      intro u _
      have hdz : ((d : ℕ) : ℤ) = (t.1.2 : ℤ) - t.1.1 := by
        rw [hd, Nat.cast_sub (by omega : t.1.1 ≤ t.1.2)]
      constructor <;> rintro ⟨v, hv⟩ <;> exact ⟨v, by linarith [hdz, hv]⟩
    rw [heq]
    have hcnt := pell_count_le (X := X) h1 h2 hd1
    -- `d² ≤ X^{2η}`
    have hdR : (d : ℝ) ≤ (X : ℝ) ^ η := by
      have := (Hcut_le hη (show 1 ≤ X by omega)).1
      have : (d : ℝ) ≤ H := by exact_mod_cast hdH
      linarith
    have hd2 : (d : ℝ) ^ 2 ≤ (X : ℝ) ^ (2 * η) := by
      rw [show 2 * η = η * (2 : ℕ) by push_cast; ring, Real.rpow_mul_natCast hX0R.le]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hdR 2
    -- `log₂(2√e₁X) + 1 ≤ (15/(ε log 2) + 1) X^{ε/3}`
    have hX3 : (X : ℝ) ^ (3 : ℝ) = X * X * X := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have he1R : (1 : ℝ) ≤ t.2.1 := by exact_mod_cast h1
    have hsq : Real.sqrt (t.2.1 : ℝ) ≤ X * X * X := by
      have h1' : Real.sqrt (t.2.1 : ℝ) ≤ t.2.1 := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
      have h2' : (t.2.1 : ℝ) ≤ M := by exact_mod_cast h1M
      calc Real.sqrt (t.2.1 : ℝ) ≤ t.2.1 := h1'
        _ ≤ M := h2'
        _ ≤ (X : ℝ) ^ (3 : ℝ) := hMle
        _ = X * X * X := hX3
    have hX2 : (2 : ℝ) ≤ X := by
      have : (16 : ℝ) ≤ X := by exact_mod_cast hX16
      linarith
    have hB0 : 0 < 2 * Real.sqrt (t.2.1 : ℝ) * X := by
      have : 0 < Real.sqrt (t.2.1 : ℝ) := Real.sqrt_pos.mpr (by linarith)
      positivity
    have hB5 : 2 * Real.sqrt (t.2.1 : ℝ) * X ≤ (X : ℝ) ^ 5 := by
      have hsq0 : 0 ≤ Real.sqrt (t.2.1 : ℝ) := Real.sqrt_nonneg _
      calc 2 * Real.sqrt (t.2.1 : ℝ) * X ≤ (X : ℝ) * (X * X * X) * X := by
            apply mul_le_mul_of_nonneg_right _ hX0R.le
            exact mul_le_mul hX2 hsq hsq0 hX0R.le
        _ = (X : ℝ) ^ 5 := by ring
    have hlogB : Real.log (2 * Real.sqrt (t.2.1 : ℝ) * X) ≤ 5 * Real.log X := by
      have := Real.log_le_log hB0 hB5
      rwa [Real.log_pow] at this
    have hlogX : Real.log X ≤ (X : ℝ) ^ (ε / 3) / (ε / 3) :=
      Real.log_le_rpow_div hX0R.le (by linarith)
    have hXe1 : (1 : ℝ) ≤ (X : ℝ) ^ (ε / 3) := Real.one_le_rpow hX1R (by linarith)
    have hlb : Real.logb 2 (2 * Real.sqrt (t.2.1 : ℝ) * X) + 1 ≤ C * (X : ℝ) ^ (ε / 3) := by
      rw [Real.logb, hCdef]
      have hA : Real.log (2 * Real.sqrt (t.2.1 : ℝ) * X) / Real.log 2 ≤
          5 * ((X : ℝ) ^ (ε / 3) / (ε / 3)) / Real.log 2 := by
        apply div_le_div_of_nonneg_right _ hl2.le
        linarith
      have hB : 5 * ((X : ℝ) ^ (ε / 3) / (ε / 3)) / Real.log 2 =
          15 / (ε * Real.log 2) * (X : ℝ) ^ (ε / 3) := by
        field_simp
        ring
      rw [hB] at hA
      nlinarith
    calc ((((Finset.Icc 1 X).filter
          (fun u : ℕ => ∃ v : ℕ, (t.2.1 : ℤ) * (u : ℤ) ^ 2 - d = t.2.2 * (v : ℤ) ^ 2)).card : ℕ) : ℝ)
        ≤ (d : ℝ) ^ 2 * (Real.logb 2 (2 * Real.sqrt (t.2.1 : ℝ) * X) + 1) := hcnt
      _ ≤ (X : ℝ) ^ (2 * η) * (C * (X : ℝ) ^ (ε / 3)) := by
          apply mul_le_mul hd2 hlb _ (by positivity)
          have : 0 ≤ Real.logb 2 (2 * Real.sqrt (t.2.1 : ℝ) * X) := by
            apply Real.logb_nonneg (by norm_num)
            have : (1 : ℝ) ≤ Real.sqrt (t.2.1 : ℝ) := Real.one_le_sqrt.mpr he1R
            nlinarith
          linarith
      _ = C * (X : ℝ) ^ (2 * η + ε / 3) := by
          rw [Real.rpow_add hX0R]; ring
      _ ≤ C * (X : ℝ) ^ ε := by
          apply mul_le_mul_of_nonneg_left _ hC0.le
          exact Real.rpow_le_rpow_of_exponent_le hX1R (by linarith)
  have hcard := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hsum : ((∑ t ∈ I, ((pellSol X t.2.1 t.2.2 ((t.1.1 : ℤ) - t.1.2)).image
      (fun u => t.2.1 * u ^ 2 + t.1.1)).card : ℕ) : ℝ) ≤ (I.card : ℝ) * (max C 0 * (X : ℝ) ^ ε) := by
    push_cast
    calc ∑ t ∈ I, (((pellSol X t.2.1 t.2.2 ((t.1.1 : ℤ) - t.1.2)).image
          (fun u => t.2.1 * u ^ 2 + t.1.1)).card : ℝ)
        ≤ ∑ _t ∈ I, max C 0 * (X : ℝ) ^ ε := by
          apply Finset.sum_le_sum
          intro t ht
          calc _ ≤ ((pellSol X t.2.1 t.2.2 ((t.1.1 : ℤ) - t.1.2)).card : ℝ) := by
                exact_mod_cast Finset.card_image_le
            _ ≤ C * (X : ℝ) ^ ε := hfib t ht
            _ ≤ max C 0 * (X : ℝ) ^ ε :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hIcard : (I.card : ℝ) ≤ ((H : ℝ) + 1) ^ 2 * ((M : ℝ) * (1 + Real.log M)) := by
    rw [hI, Finset.card_product]
    push_cast
    have h1 : ((((Finset.range (H + 1)) ×ˢ (Finset.range (H + 1))).filter
        (fun ij : ℕ × ℕ => ij.1 < ij.2)).card : ℝ) ≤ ((H : ℝ) + 1) ^ 2 := by
      have := Finset.card_filter_le ((Finset.range (H + 1)) ×ˢ (Finset.range (H + 1)))
        (fun ij : ℕ × ℕ => ij.1 < ij.2)
      rw [Finset.card_product, Finset.card_range] at this
      have : ((((Finset.range (H + 1)) ×ˢ (Finset.range (H + 1))).filter
          (fun ij : ℕ × ℕ => ij.1 < ij.2)).card : ℝ) ≤ ((H + 1) * (H + 1) : ℕ) := by
        exact_mod_cast this
      push_cast at this; nlinarith
    have h2 := card_pairs_le M
    apply mul_le_mul h1 h2 (by positivity) (by positivity)
  calc ((smallSet σ η X).card : ℝ) ≤ (I.card : ℝ) * (max C 0 * (X : ℝ) ^ ε) := by
        exact le_trans (by exact_mod_cast hcard) hsum
    _ ≤ ((H : ℝ) + 1) ^ 2 * ((M : ℝ) * (1 + Real.log M)) * (max C 0 * (X : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_right hIcard (by positivity)
    _ = max C 0 * ((H : ℝ) + 1) ^ 2 * ((M : ℝ) * (1 + Real.log M)) * (X : ℝ) ^ ε := by ring

end Erdos374.D35

end
