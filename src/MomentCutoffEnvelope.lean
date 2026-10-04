import PowerBandCountEnvelope
import MomentThreshold

/-!
A uniform lower bound for the amplitude cutoff when the moment order
varies between two and three. This extends ProductCutoffEnvelope to
arbitrary fixed polynomial lower bounds and either sign of the budget
exponent. It supplies the band-count hypothesis; no level bound is assumed
to follow from this purely algebraic estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter

namespace MomentCutoffEnvelope
open MomentThreshold SupremumMoment

theorem cutoff_lower (B X c a b p : ℝ)
    (hX : 1 ≤ X) (hc : 0 < c) (hc1 : c ≤ 1) (ha : 0 ≤ a)
    (_hp : 2 ≤ p) (hp3 : p ≤ 3) (hB : c / X ^ a ≤ B) :
    c / X ^ (a + max b 0) ≤ cutoff B (X ^ b) p := by
  have hXp : 0 < X := by linarith
  have hμ : 0 < X ^ b := Real.rpow_pos_of_pos hXp _
  have hBp : 0 < B := (div_pos hc (by positivity)).trans_le hB
  have hab : 0 ≤ a + max b 0 := add_nonneg ha (le_max_right _ _)
  have hbasepos : 0 < c / X ^ (a + max b 0) := by positivity
  have hbaseone : c / X ^ (a + max b 0) ≤ 1 := by
    exact (div_le_one (by positivity)).mpr (hc1.trans (Real.one_le_rpow hX hab))
  have hbase : c / X ^ (a + max b 0) ≤ B / X ^ b := by
    calc
      _ = (c / X ^ a) / X ^ (max b 0) := by
        rw [Real.rpow_add hXp]
        field_simp
      _ ≤ B / X ^ (max b 0) := div_le_div_of_nonneg_right hB (by positivity)
      _ ≤ B / X ^ b := div_le_div_of_nonneg_left hBp.le hμ
        (Real.rpow_le_rpow_of_exponent_le hX (le_max_left _ _))
  have hepos : 0 ≤ 1 / (6 - p) := div_nonneg (by norm_num) (by linarith)
  have heone : 1 / (6 - p) ≤ 1 := by
    exact (div_le_one (by linarith)).mpr (by linarith)
  exact (Real.self_le_rpow_of_le_one hbasepos.le hbaseone heone).trans
    (Real.rpow_le_rpow hbasepos.le hbase hepos)

theorem eventually_band_bound (c a b u δ : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (ha : 0 ≤ a) (hu : 0 ≤ u) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ (B U p : ℝ),
      2 ≤ p → p ≤ 3 → c / X ^ a ≤ B → U ≤ X ^ u →
      bandCountBound (cutoff B (X ^ b) p) U ≤ X ^ δ := by
  filter_upwards [BandCountEnvelope.eventually_bound_of_powers
    c (a + max b 0) u δ hc hc1 (add_nonneg ha (le_max_right _ _)) hu hδ]
    with X hX
  refine ⟨hX.1, ?_⟩
  intro B U p hp hp3 hB hU
  exact hX.2 _ _ (cutoff_lower B X c a b p hX.1 hc hc1 ha hp hp3 hB) hU

end MomentCutoffEnvelope

#print axioms MomentCutoffEnvelope.eventually_band_bound
run_cmd do
  for target in [``MomentCutoffEnvelope.cutoff_lower,
      ``MomentCutoffEnvelope.eventually_band_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "MOMENT CUTOFF ENVELOPE PASSED"
