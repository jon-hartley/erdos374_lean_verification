import HarmanMomentSelection

/-!
Conjugate moment orders and their uniform bounds. A small increase of
the single-factor order changes the paired length threshold by at most
that increase; a fixed length margin can therefore pay for the change.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace PairedMomentOrder
open HarmanMomentSelection

theorem paired_eq (beta : ℝ) (hbeta : 2 < beta) :
    pairedOrder beta = 2 + 4 / (beta - 2) := by
  have hd : beta - 2 ≠ 0 := ne_of_gt (by linarith)
  unfold pairedOrder
  field_simp
  ring

theorem conjugate (beta : ℝ) (hbeta : 2 < beta) :
    2 < pairedOrder beta ∧ 2 / pairedOrder beta + 2 / beta = 1 := by
  have hb : 0 < beta := by linarith
  have hd : 0 < beta - 2 := by linarith
  constructor
  · rw [paired_eq beta hbeta]
    have hh : 0 < 4 / (beta - 2) := div_pos (by norm_num) hd
    linarith
  · unfold pairedOrder
    field_simp
    ring

theorem bounds (H : ℕ) (beta : ℝ) (hH : 1 ≤ H)
    (hbeta : 8 ≤ beta) (hupper : beta ≤ 2 * (H : ℝ) + 2) :
    2 + 1 / ((H : ℝ) + 1) ≤ pairedOrder beta ∧ pairedOrder beta ≤ 3 := by
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hd : 0 < beta - 2 := by linarith
  rw [paired_eq beta (by linarith)]
  constructor
  · have hh : 1 / ((H : ℝ) + 1) ≤ 4 / (beta - 2) := by
      apply (div_le_div_iff₀ (by positivity) hd).mpr
      linarith
    linarith
  · have hh : 4 / (beta - 2) ≤ 1 := (div_le_one hd).mpr (by linarith)
    linarith

theorem threshold_shift (beta ξ : ℝ) (hbeta : 8 ≤ beta) (hξ : 0 ≤ ξ) :
    4 / (2 + pairedOrder (beta + ξ)) ≤ 4 / (2 + pairedOrder beta) + ξ := by
  rw [paired_threshold (beta + ξ) (by linarith), paired_threshold beta (by linarith)]
  have hd : 0 < beta - 1 := by linarith
  have he : 0 < beta + ξ - 1 := by linarith
  have hid : (beta + ξ - 2) / (beta + ξ - 1) - (beta - 2) / (beta - 1) =
      ξ / ((beta + ξ - 1) * (beta - 1)) := by
    field_simp
    ring
  have hden : 1 ≤ (beta + ξ - 1) * (beta - 1) := by
    nlinarith [sq_nonneg (beta - 1), mul_nonneg hξ (show 0 ≤ beta - 1 by linarith)]
  have hh : ξ / ((beta + ξ - 1) * (beta - 1)) ≤ ξ :=
    div_le_self hξ hden
  linarith

theorem margin_after_shift (beta ξ t q η : ℝ)
    (hbeta : 8 ≤ beta) (hξ : 0 ≤ ξ) (hξη : ξ ≤ η / 2)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hq : 4 / (2 + pairedOrder beta) * t + η ≤ q) :
    4 / (2 + pairedOrder (beta + ξ)) * t + η / 2 ≤ q := by
  have hh := mul_le_mul_of_nonneg_right (threshold_shift beta ξ hbeta hξ) ht
  have hξt := mul_le_of_le_one_right hξ ht1
  nlinarith

end PairedMomentOrder

#print axioms PairedMomentOrder.bounds
#print axioms PairedMomentOrder.margin_after_shift
run_cmd do
  for target in [``PairedMomentOrder.paired_eq, ``PairedMomentOrder.conjugate,
      ``PairedMomentOrder.bounds, ``PairedMomentOrder.threshold_shift,
      ``PairedMomentOrder.margin_after_shift] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "PAIRED MOMENT ORDER PASSED"
