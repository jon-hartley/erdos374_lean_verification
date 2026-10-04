import TripleAdoptEighthParameterEnvelope
import BandCountEnvelope

/-!
The eighth-moment amplitude cutoff cannot be smaller than a fixed
multiple of X^(-2). Thus its band-count loss is absorbed uniformly.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter

namespace TripleAdoptEighthCutoffEnvelope
open EighthMomentParameters TripleAdoptEighthParameterEnvelope NormalizedPowerLevel
open DyadicLevelParameters SupremumMoment MomentThreshold

def lowerConstant (D : ℝ) : ℝ := min 1 (sexticConstant * D ^ 3)

theorem lowerConstant_positive (D : ℝ) (hD : 0 < D) : 0 < lowerConstant D := by
  unfold lowerConstant sexticConstant
  positivity

theorem cutoff_lower (D : ℝ) (N : ℕ) (T X α κ : ℝ)
    (hD : 0 < D) (hN : 1 ≤ N) (hNX : (N : ℝ) ≤ X)
    (hT : 1 ≤ T) (hα : 0 ≤ α) (hκ : 0 ≤ κ) :
    (lowerConstant D) ^ (3 / 10 : ℝ) / X ^ 2 ≤
      cutoff (sextic (N ^ 3) 3 T (energyBudget D N 3 α 1)) (X ^ (-κ)) (8 / 3) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX : 1 ≤ X := hNR.trans hNX
  have hXp : 0 < X := by linarith
  have hc : 0 < lowerConstant D := lowerConstant_positive D hD
  have hμ : 0 < X ^ (-κ) := Real.rpow_pos_of_pos hXp _
  have hμ1 : X ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)
  let B := sextic (N ^ 3) 3 T (energyBudget D N 3 α 1)
  have hBlower : lowerConstant D / X ^ 6 ≤ B :=
    (div_le_div_of_nonneg_right (min_le_right 1 (sexticConstant * D ^ 3)) (by positivity)).trans
      (sextic_lower D N T X α hD hN hNX hT hα)
  have hB : 0 < B := (div_pos hc (by positivity)).trans_le hBlower
  have hquot : lowerConstant D / X ^ 6 ≤ B / X ^ (-κ) := by
    apply hBlower.trans
    exact (le_div_iff₀ hμ).mpr (mul_le_of_le_one_right hB.le hμ1)
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ lowerConstant D / X ^ 6)
    hquot (by norm_num : (0 : ℝ) ≤ 3 / 10)
  have hden : (X ^ 6) ^ (3 / 10 : ℝ) ≤ X ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast_mul hXp.le, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hX
    norm_num
  calc
    _ ≤ (lowerConstant D) ^ (3 / 10 : ℝ) / (X ^ 6) ^ (3 / 10 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = (lowerConstant D / X ^ 6) ^ (3 / 10 : ℝ) :=
      (Real.div_rpow hc.le (by positivity) _).symm
    _ ≤ (B / X ^ (-κ)) ^ (3 / 10 : ℝ) := hpow
    _ = _ := by dsimp [cutoff, B]; norm_num

theorem eventually_band_bound (D α κ δ : ℝ) (hD : 0 < D)
    (hα : 0 ≤ α) (hκ : 0 ≤ κ) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ (N : ℕ) (T : ℝ),
      1 ≤ N → (N : ℝ) ≤ X → 1 ≤ T →
      bandCountBound
        (cutoff (sextic (N ^ 3) 3 T (energyBudget D N 3 α 1)) (X ^ (-κ)) (8 / 3))
        (X ^ (-3 * κ)) ≤ X ^ δ := by
  have hc : 0 < lowerConstant D := lowerConstant_positive D hD
  have hc1 : lowerConstant D ≤ 1 := min_le_left _ _
  have hroot : 0 < (lowerConstant D) ^ (3 / 10 : ℝ) := Real.rpow_pos_of_pos hc _
  have hroot1 : (lowerConstant D) ^ (3 / 10 : ℝ) ≤ 1 :=
    Real.rpow_le_one hc.le hc1 (by norm_num)
  filter_upwards [BandCountEnvelope.eventually_bound _ δ hroot hroot1 hδ] with X hX
  refine ⟨hX.1, ?_⟩
  intro N T hN hNX hT
  apply hX.2
  · exact cutoff_lower D N T X α κ hD hN hNX hT hα hκ
  · exact Real.rpow_le_one_of_one_le_of_nonpos hX.1 (by nlinarith)

end TripleAdoptEighthCutoffEnvelope

#print axioms TripleAdoptEighthCutoffEnvelope.eventually_band_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``TripleAdoptEighthCutoffEnvelope.eventually_band_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "EIGHTH CUTOFF ENVELOPE PASSED"
