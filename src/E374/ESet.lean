import E374.D3Short
import E374.Kernel

/-!
# The nonconsecutive three-factor endpoints `E` and their small/large-kernel split

`ESet = {m : ∃ a h, 2 ≤ h ∧ a + h < m ∧ q_a P_h(m) = □}` (here `a = 0` is allowed;
`q_0 = 1`, which also covers the two-factor blocks `P_ℓ(m) = □`, `ℓ ≥ 2`).

For a splitting exponent `σ` and the shortness exponent `η`, every endpoint `m ≤ X` of
`ESet` lies in the *small-kernel* set (some configuration with `q_a ≤ (X^σ)^h`) or in one
of the *large-kernel* fibres `T a h` with `a ≤ H`, `2 ≤ h ≤ H`, `(X^σ)^h < q_a`,
where `H = ⌊X^η⌋`.
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

/-- Nonconsecutive three-factor (and `≥ 2`-block two-factor) endpoints. -/
def ESet : Set ℕ :=
  {m | ∃ a h : ℕ, 2 ≤ h ∧ a + h < m ∧ IsSquare (q a * falling h m)}

/-- `H = ⌊X^η⌋`. -/
def Hcut (η : ℝ) (X : ℕ) : ℕ := ⌊(X : ℝ) ^ η⌋₊

/-- The large-kernel fibre for fixed `(a, h)`. -/
def fibre (X a h : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun m => a + h < m ∧ IsSquare (q a * falling h m))

open Classical in
/-- The small-kernel endpoints. -/
def smallSet (σ η : ℝ) (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun m => ∃ a h : ℕ, a ≤ Hcut η X ∧ 2 ≤ h ∧ h ≤ Hcut η X ∧
    a + h < m ∧ IsSquare (q a * falling h m) ∧ (q a : ℝ) ≤ ((X : ℝ) ^ σ) ^ h)

open Classical in
/-- Pairs `(a, h)` in the large-kernel regime. -/
def largePairs (σ η : ℝ) (X : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (Hcut η X + 1)) ×ˢ (Finset.Icc 2 (Hcut η X))).filter
    (fun ah => ((X : ℝ) ^ σ) ^ ah.2 < (q ah.1 : ℝ))

/-- **Decomposition of `E`.** -/
theorem prefixCount_ESet_le (hRM : Tasks.ValuationOneMass) (hG : Tasks.FactorialClassGrowth)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) (σ : ℝ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      prefixCount ESet X ≤
        (smallSet σ η X).card + ∑ ah ∈ largePairs σ η X, (fibre X ah.1 ah.2).card := by
  classical
  obtain ⟨N, hN⟩ := uniform_short hRM hG hη hη1
  refine ⟨max N 1, fun X hX => ?_⟩
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_right N 1) hX
  have hsub : (Finset.Icc 1 X).filter (fun m => m ∈ ESet) ⊆
      smallSet σ η X ∪ (largePairs σ η X).biUnion (fun ah => fibre X ah.1 ah.2) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmI, a, h, hh, hahm, hs⟩ := hm
    have hmX : m ≤ X := (Finset.mem_Icc.mp hmI).2
    obtain ⟨hshort, ha⟩ := hN X hXN m a h hmX (by omega) hahm hs
    have hhH : h ≤ Hcut η X := by
      apply Nat.le_floor
      have : (X : ℝ) ^ (η / 2) ≤ (X : ℝ) ^ η :=
        Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      linarith
    have haH : a ≤ Hcut η X := Nat.le_floor ha.le
    by_cases hk : (q a : ℝ) ≤ ((X : ℝ) ^ σ) ^ h
    · apply Finset.mem_union_left
      rw [smallSet, Finset.mem_filter]
      exact ⟨hmI, a, h, haH, hh, hhH, hahm, hs, hk⟩
    · push_neg at hk
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨(a, h), ?_, ?_⟩
      · rw [largePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_Icc]
        exact ⟨⟨by omega, hh, hhH⟩, hk⟩
      · rw [fibre, Finset.mem_filter]
        exact ⟨hmI, hahm, hs⟩
  calc prefixCount ESet X = ((Finset.Icc 1 X).filter (fun m => m ∈ ESet)).card := by
        unfold prefixCount; congr
    _ ≤ (smallSet σ η X ∪ (largePairs σ η X).biUnion (fun ah => fibre X ah.1 ah.2)).card :=
        Finset.card_le_card hsub
    _ ≤ (smallSet σ η X).card + ((largePairs σ η X).biUnion (fun ah => fibre X ah.1 ah.2)).card :=
        Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left Finset.card_biUnion_le _

/-- Number of large-kernel pairs. -/
theorem card_largePairs_le (σ η : ℝ) (X : ℕ) :
    (largePairs σ η X).card ≤ (Hcut η X + 1) * (Hcut η X + 1) := by
  classical
  unfold largePairs
  calc _ ≤ ((Finset.range (Hcut η X + 1)) ×ˢ (Finset.Icc 2 (Hcut η X))).card :=
        Finset.card_filter_le _ _
    _ = (Hcut η X + 1) * (Hcut η X + 1 - 2) := by
        rw [Finset.card_product, Finset.card_range, Nat.card_Icc]
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

/-- `H ≤ X^η` and `H + 1 ≤ 2 X^η` for `X ≥ 1`, `η ≥ 0`. -/
theorem Hcut_le {η : ℝ} (hη : 0 ≤ η) {X : ℕ} (hX : 1 ≤ X) :
    (Hcut η X : ℝ) ≤ (X : ℝ) ^ η ∧ ((Hcut η X : ℝ) + 1) ≤ 2 * (X : ℝ) ^ η := by
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have h1 : (1 : ℝ) ≤ (X : ℝ) ^ η := Real.one_le_rpow hX1 hη
  have h2 : (Hcut η X : ℝ) ≤ (X : ℝ) ^ η := Nat.floor_le (by positivity)
  exact ⟨h2, by linarith⟩

end Erdos374.D35

end
