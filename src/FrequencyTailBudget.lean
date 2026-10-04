import SmoothedFrequencyTail

/-!
The frequency tail above X^(1-theta+kappa) has a relative power saving
for windows at least X^theta, once its actual polynomial energy has
arbitrarily small power growth. All exponents precede the ambient X.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set

namespace FrequencyTailBudget
open SmoothedWindowTransfer

theorem eventually_separated (θ κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (Y ε a b H : ℝ) (F : ℝ → ℂ),
        X ^ θ ≤ Y → Y < X → ε ∈ Ioo 0 1 →
        X ^ (1 - θ + κ) ≤ H → a ≤ b → b - a ≤ X →
        (∀ t ∈ Icc a b, H ≤ |t|) → Continuous F →
        (∫ t in Icc a b, ‖F t‖ ^ 2) ≤ X ^ (κ / 2) →
        (1 / X) * (∫ x in Icc X (2 * X),
          ‖transform F MellinSmoothingFunction.smoothing ε a b
            (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
              Y ^ 2 * X ^ (-κ) := by
  let C := 32768 * Real.exp 2
  filter_upwards [PolynomialLogEnvelope.eventually_bound C 1 (κ / 2)
    (by dsimp [C]; positivity) (by positivity),
    eventually_ge_atTop (Real.exp 1)] with X hconstant hX
  refine ⟨hX, ?_⟩
  intro Y ε a b H F hYlow hYX hε hHlow hab hlen hband hF henergy
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hY : 0 ≤ Y := (Real.rpow_pos_of_pos hXp θ).le.trans hYlow
  have hH : 0 < H := (Real.rpow_pos_of_pos hXp _).trans_le hHlow
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hconstant.1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hClog : C * Real.log X ≤ X ^ (κ / 2) := by
    calc
      _ ≤ C * (1 + Real.log X) := mul_le_mul_of_nonneg_left (by linarith) hC
      _ ≤ _ := by simpa only [pow_one] using hconstant.2
  have hHsq : X ^ (2 * (1 - θ + κ)) ≤ H ^ (2 : ℕ) := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hHlow 2
    rw [← Real.rpow_mul_natCast hXp.le] at hh
    simpa only [Nat.cast_ofNat, mul_comm (1 - θ + κ) (2 : ℝ)] using hh
  have hYsq : X ^ (2 * θ) ≤ Y ^ (2 : ℕ) := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hYlow 2
    rw [← Real.rpow_mul_natCast hXp.le] at hh
    simpa only [Nat.cast_ofNat, mul_comm θ (2 : ℝ)] using hh
  apply (SmoothedFrequencyTail.separated_band_bound X Y ε a b H (X ^ (κ / 2)) F
    hX hY hYX hε hH hab hlen hband hF henergy).trans
  calc
    _ = (C * Real.log X) * X ^ (2 : ℕ) * X ^ (κ / 2) / H ^ (2 : ℕ) := by
      dsimp [C]
      ring
    _ ≤ X ^ (κ / 2) * X ^ (2 : ℕ) * X ^ (κ / 2) /
        X ^ (2 * (1 - θ + κ)) := by gcongr
    _ = X ^ (2 * θ) * X ^ (-κ) := by
      rw [← Real.rpow_natCast X 2,
        ← Real.rpow_add hXp, ← Real.rpow_add hXp, ← Real.rpow_sub hXp,
        ← Real.rpow_add hXp]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hYsq (by positivity)

theorem eventually_bound (θ κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (Y ε H : ℝ) (F : ℝ → ℂ),
        X ^ θ ≤ Y → Y < X → ε ∈ Ioo 0 1 →
        X ^ (1 - θ + κ) ≤ H → H ≤ X → Continuous F →
        (∫ t in Icc H X, ‖F t‖ ^ 2) ≤ X ^ (κ / 2) →
        (1 / X) * (∫ x in Icc X (2 * X),
          ‖transform F MellinSmoothingFunction.smoothing ε H X
            (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
              Y ^ 2 * X ^ (-κ) := by
  filter_upwards [eventually_separated θ κ hκ] with X hX
  refine ⟨hX.1, ?_⟩
  intro Y ε H F hYlow hYX hε hHlow hHX hF henergy
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX.1
  have hH : 0 < H := (Real.rpow_pos_of_pos hXp _).trans_le hHlow
  exact hX.2 Y ε H X H F hYlow hYX hε hHlow hHX (by linarith)
    (fun t ht => ht.1.trans (le_abs_self t)) hF henergy

theorem eventually_negative_bound (θ κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (Y ε H : ℝ) (F : ℝ → ℂ),
        X ^ θ ≤ Y → Y < X → ε ∈ Ioo 0 1 →
        X ^ (1 - θ + κ) ≤ H → H ≤ X → Continuous F →
        (∫ t in Icc (-X) (-H), ‖F t‖ ^ 2) ≤ X ^ (κ / 2) →
        (1 / X) * (∫ x in Icc X (2 * X),
          ‖transform F MellinSmoothingFunction.smoothing ε (-X) (-H)
            (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
              Y ^ 2 * X ^ (-κ) := by
  filter_upwards [eventually_separated θ κ hκ] with X hX
  refine ⟨hX.1, ?_⟩
  intro Y ε H F hYlow hYX hε hHlow hHX hF henergy
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX.1
  have hH : 0 < H := (Real.rpow_pos_of_pos hXp _).trans_le hHlow
  apply hX.2 Y ε (-X) (-H) H F hYlow hYX hε hHlow (by linarith)
    (by linarith) ?_ hF henergy
  intro t ht
  have hh := neg_le_abs t
  linarith [ht.2]

end FrequencyTailBudget

#print axioms FrequencyTailBudget.eventually_bound
run_cmd do
  for target in [``FrequencyTailBudget.eventually_separated,
      ``FrequencyTailBudget.eventually_bound,
      ``FrequencyTailBudget.eventually_negative_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FREQUENCY TAIL BUDGET PASSED"
