import CompactIntegral

/-!
Select a real moment order from the exponent inequalities in Harman's
Lemma 5. The variables t, g, and q are base-X logarithms of the
segment, single-factor, and paired-factor lengths.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace HarmanMomentSelection

def pairedOrder (beta : ℝ) : ℝ := 2 * beta / (beta - 2)

theorem paired_threshold (beta : ℝ) (hbeta : 2 < beta) :
    4 / (2 + pairedOrder beta) = (beta - 2) / (beta - 1) := by
  have htwo : beta - 2 ≠ 0 := by linarith
  have hone : beta - 1 ≠ 0 := by linarith
  have hsum : 2 + pairedOrder beta =
      4 * (beta - 1) / (beta - 2) := by
    unfold pairedOrder
    field_simp
    ring
  rw [hsum]
  field_simp

theorem interior_coefficient (h beta : ℝ)
    (hh : 4 ≤ h) (hbeta : 2 * h ≤ beta) :
    (beta - 2) / (beta - 1) ≤ 10 / 9 - 4 / (beta + 2 * h) := by
  have hleft : 0 < beta - 1 := by linarith
  have hright : 0 < beta + 2 * h := by linarith
  have hden : 0 < 9 * (beta - 1) * (beta + 2 * h) := by positivity
  have hidentity :
      (10 / 9 - 4 / (beta + 2 * h) -
        (beta - 2) / (beta - 1)) *
          (9 * (beta - 1) * (beta + 2 * h)) =
        (beta - 10) ^ 2 + 2 * (h - 4) * (beta + 8) := by
    field_simp
    ring
  have hnonneg :
      0 ≤ (beta - 10) ^ 2 + 2 * (h - 4) * (beta + 8) := by
    have hpart : 0 ≤ 2 * (h - 4) * (beta + 8) := by
      apply mul_nonneg
      · apply mul_nonneg <;> linarith
      · linarith
    nlinarith [sq_nonneg (beta - 10)]
  have hdiff : 0 ≤ 10 / 9 - 4 / (beta + 2 * h) -
      (beta - 2) / (beta - 1) := by
    by_contra hnegative
    have hhnegative :
        (10 / 9 - 4 / (beta + 2 * h) -
          (beta - 2) / (beta - 1)) *
            (9 * (beta - 1) * (beta + 2 * h)) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hnegative) hden
    rw [hidentity] at hhnegative
    linarith
  linarith

theorem interior_margin (h beta t g q e : ℝ)
    (hh : 4 ≤ h) (hbeta : 2 * h ≤ beta) (ht : 0 ≤ t)
    (hbalance : g * (beta + 2 * h) = 4 * t)
    (hproduct : q + g ≥ (10 / 9) * t + e / 10) :
    q ≥ 4 * t / (2 + pairedOrder beta) + e / 10 := by
  have hden : 0 < beta + 2 * h := by linarith
  have hbetaTwo : 2 < beta := by linarith
  have hg : g = 4 * t / (beta + 2 * h) := by
    apply (eq_div_iff hden.ne').mpr
    linear_combination hbalance
  have hcoeff := interior_coefficient h beta hh hbeta
  have hmult := mul_le_mul_of_nonneg_right hcoeff ht
  have hrewrite : 4 * t / (2 + pairedOrder beta) =
      (beta - 2) / (beta - 1) * t := by
    calc
      _ = (4 / (2 + pairedOrder beta)) * t := by ring
      _ = _ := by rw [paired_threshold beta hbetaTwo]
  rw [hrewrite]
  rw [hg] at hproduct
  have hrewriteG : 4 * t / (beta + 2 * h) =
      (4 / (beta + 2 * h)) * t := by ring
  rw [hrewriteG] at hproduct
  nlinarith [hmult]

theorem jump_coefficient (beta : ℝ) (hbeta : 10 ≤ beta) :
    (beta - 2) / (beta - 1) ≤ 10 / 9 - 2 / (beta - 1) := by
  have hden : 0 < beta - 1 := by linarith
  have hidentity :
      (10 / 9 - 2 / (beta - 1) -
        (beta - 2) / (beta - 1)) * (9 * (beta - 1)) = beta - 10 := by
    field_simp
    ring
  have hdiff : 0 ≤ 10 / 9 - 2 / (beta - 1) -
      (beta - 2) / (beta - 1) := by
    by_contra hnegative
    have hhnegative :
        (10 / 9 - 2 / (beta - 1) -
          (beta - 2) / (beta - 1)) * (9 * (beta - 1)) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hnegative) (by positivity)
    rw [hidentity] at hhnegative
    linarith
  linarith

theorem jump_margin (beta t g q e : ℝ)
    (hbeta : 10 ≤ beta) (ht : 0 ≤ t)
    (hprevious : g * (beta - 1) ≤ 2 * t)
    (hproduct : q + g ≥ (10 / 9) * t + e / 10) :
    q ≥ 4 * t / (2 + pairedOrder beta) + e / 10 := by
  have hden : 0 < beta - 1 := by linarith
  have hbetaTwo : 2 < beta := by linarith
  have hg : g ≤ 2 * t / (beta - 1) :=
    (le_div_iff₀ hden).mpr hprevious
  have hcoeff := jump_coefficient beta hbeta
  have hmult := mul_le_mul_of_nonneg_right hcoeff ht
  have hrewrite : 4 * t / (2 + pairedOrder beta) =
      (beta - 2) / (beta - 1) * t := by
    calc
      _ = (4 / (2 + pairedOrder beta)) * t := by ring
      _ = _ := by rw [paired_threshold beta hbetaTwo]
  rw [hrewrite]
  have hrewriteG : 2 * t / (beta - 1) =
      (2 / (beta - 1)) * t := by ring
  rw [hrewriteG] at hg
  nlinarith [hmult]

theorem exists_order_with_bounds (t g q e : ℝ)
    (ht : 0 ≤ t) (hg : 0 < g) (he : 0 < e)
    (hproduct : q + g ≥ (10 / 9) * t + e / 10)
    (hpair : q ≥ (6 / 7) * t + e) :
    ∃ h : ℕ, ∃ beta : ℝ,
      4 ≤ h ∧ 2 * (h : ℝ) ≤ beta ∧ beta ≤ 2 * (h : ℝ) + 2 ∧
        g * (beta + 2 * h) ≥ 4 * t ∧
          q ≥ 4 * t / (2 + pairedOrder beta) + e / 10 ∧
            (h : ℝ) ≤ t / g + 4 ∧ beta ≤ 2 * (t / g) + 8 := by
  let y : ℝ := t / g
  have hy_nonneg : 0 ≤ y := div_nonneg ht hg.le
  have hgy : g * y = t := by
    dsimp [y]
    field_simp
  by_cases hy_four : y ≤ 4
  · refine ⟨4, 8, by omega, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
    · have htg : t ≤ 4 * g := by
        rw [← hgy]
        simpa only [mul_comm] using
          (mul_le_mul_of_nonneg_left hy_four hg.le)
      norm_num
      linarith
    · have hthreshold : 4 * t / (2 + pairedOrder 8) =
          (6 / 7) * t := by
        norm_num [pairedOrder]
        ring
      rw [hthreshold]
      linarith
    · dsimp [y] at hy_nonneg
      linarith
    · dsimp [y] at hy_nonneg
      linarith
  · have hy_gt : 4 < y := lt_of_not_ge hy_four
    let hNat : ℕ := ⌊y⌋₊
    have hfloor_le : (hNat : ℝ) ≤ y := Nat.floor_le hy_nonneg
    have hfloor_lt : y < (hNat : ℝ) + 1 := Nat.lt_floor_add_one y
    have hNat_four : 4 ≤ hNat := by
      by_contra hnot
      have hsmall : hNat ≤ 3 := by omega
      have hsmall_real : (hNat : ℝ) ≤ 3 := by exact_mod_cast hsmall
      linarith
    by_cases hy_half : y ≤ (hNat : ℝ) + 1 / 2
    · let beta : ℝ := 4 * y - 2 * (hNat : ℝ)
      have hNat_real : (4 : ℝ) ≤ hNat := by exact_mod_cast hNat_four
      have hbeta_lo : 2 * (hNat : ℝ) ≤ beta := by
        dsimp [beta]
        linarith
      have hbeta_hi : beta ≤ 2 * (hNat : ℝ) + 2 := by
        dsimp [beta]
        linarith
      have hbalance : g * (beta + 2 * hNat) = 4 * t := by
        dsimp [beta]
        nlinarith [hgy]
      refine ⟨hNat, beta, hNat_four, hbeta_lo, hbeta_hi,
        hbalance.ge, ?_, ?_, ?_⟩
      · exact interior_margin hNat beta t g q e hNat_real hbeta_lo
          ht hbalance hproduct
      · dsimp [y] at hfloor_le
        linarith
      · dsimp [beta, y] at *
        linarith
    · let hNext : ℕ := hNat + 1
      let beta : ℝ := 2 * hNext
      have hNext_five : 5 ≤ hNext := by dsimp [hNext]; omega
      have hNext_real : (5 : ℝ) ≤ hNext := by exact_mod_cast hNext_five
      have hbeta_ten : 10 ≤ beta := by dsimp [beta]; linarith
      have hbalance : g * (beta + 2 * hNext) ≥ 4 * t := by
        have hbound : t < g * (hNext : ℝ) := by
          have hmul := mul_lt_mul_of_pos_left hfloor_lt hg
          have hcast : (hNext : ℝ) = (hNat : ℝ) + 1 := by
            simp [hNext]
          rw [hcast]
          rw [hgy] at hmul
          exact hmul
        dsimp [beta]
        nlinarith
      have hprevious : g * (beta - 1) ≤ 2 * t := by
        have hhalf : (hNat : ℝ) + 1 / 2 < y := lt_of_not_ge hy_half
        have hmul := mul_lt_mul_of_pos_left hhalf hg
        dsimp [beta, hNext]
        push_cast
        nlinarith [hgy]
      refine ⟨hNext, beta, by omega, by dsimp [beta]; exact le_refl _,
        by dsimp [beta]; linarith, hbalance, ?_, ?_, ?_⟩
      · exact jump_margin beta t g q e hbeta_ten ht hprevious hproduct
      · dsimp [hNext, y]
        push_cast
        linarith
      · dsimp [beta, hNext, y]
        push_cast
        linarith

theorem exists_order (t g q e : ℝ)
    (ht : 0 ≤ t) (hg : 0 < g) (he : 0 < e)
    (hproduct : q + g ≥ (10 / 9) * t + e / 10)
    (hpair : q ≥ (6 / 7) * t + e) :
    ∃ h : ℕ, ∃ beta : ℝ,
      4 ≤ h ∧ 2 * (h : ℝ) ≤ beta ∧ beta ≤ 2 * (h : ℝ) + 2 ∧
        g * (beta + 2 * h) ≥ 4 * t ∧
          q ≥ 4 * t / (2 + pairedOrder beta) + e / 10 := by
  obtain ⟨h, beta, hh, hlo, hhi, hbal, hq, -, -⟩ :=
    exists_order_with_bounds t g q e ht hg he hproduct hpair
  exact ⟨h, beta, hh, hlo, hhi, hbal, hq⟩

theorem exists_order_uniform (t g q e lambda : ℝ)
    (ht : 0 ≤ t) (htOne : t ≤ 1)
    (hlambda : 0 < lambda) (hgle : lambda ≤ g) (he : 0 < e)
    (hproduct : q + g ≥ (10 / 9) * t + e / 10)
    (hpair : q ≥ (6 / 7) * t + e) :
    ∃ h : ℕ, ∃ beta : ℝ,
      4 ≤ h ∧ 2 * (h : ℝ) ≤ beta ∧ beta ≤ 2 * (h : ℝ) + 2 ∧
        g * (beta + 2 * h) ≥ 4 * t ∧
          q ≥ 4 * t / (2 + pairedOrder beta) + e / 10 ∧
            (h : ℝ) ≤ 1 / lambda + 4 ∧ beta ≤ 2 / lambda + 8 := by
  have hg : 0 < g := lt_of_lt_of_le hlambda hgle
  have hdiv : t / g ≤ 1 / lambda := by
    apply (div_le_iff₀ hg).mpr
    have hmul := mul_le_mul_of_nonneg_left htOne hlambda.le
    have htarget : t * lambda ≤ g := by nlinarith
    calc
      t ≤ g / lambda := (le_div_iff₀ hlambda).mpr htarget
      _ = 1 / lambda * g := by ring
  obtain ⟨h, beta, hh, hlo, hhi, hbal, hq, hbound, hbeta⟩ :=
    exists_order_with_bounds t g q e ht hg he hproduct hpair
  refine ⟨h, beta, hh, hlo, hhi, hbal, hq, ?_, ?_⟩
  · linarith
  · have hscaled : 2 * (t / g) ≤ 2 * (1 / lambda) := by linarith
    have hid : 2 / lambda = 2 * (1 / lambda) := by ring
    rw [hid]
    linarith

end HarmanMomentSelection

#print axioms HarmanMomentSelection.interior_margin
#print axioms HarmanMomentSelection.jump_margin
#print axioms HarmanMomentSelection.exists_order
#print axioms HarmanMomentSelection.exists_order_uniform
run_cmd do
  for target in [``HarmanMomentSelection.paired_threshold,
      ``HarmanMomentSelection.interior_margin,
      ``HarmanMomentSelection.jump_margin,
      ``HarmanMomentSelection.exists_order,
      ``HarmanMomentSelection.exists_order_uniform] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "HARMAN MOMENT SELECTION PASSED"
