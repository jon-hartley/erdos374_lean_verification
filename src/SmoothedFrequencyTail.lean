import SmoothedWindowTransfer

/-!
For frequencies above H, retain the window kernel's 1/abs(t) decay.
This transfers an ordinary mean-square estimate to the upper frequency
tail even when a product power-saving theorem does not reach height X.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set

namespace SmoothedFrequencyTail
open MellinWindowFactor SmoothMellinMultiplier SmoothedWindowTransfer

theorem separated_band_bound (X Y ε a b H E : ℝ) (F : ℝ → ℂ)
    (hX : Real.exp 1 ≤ X) (hY : 0 ≤ Y) (hYX : Y < X)
    (hε : ε ∈ Ioo 0 1) (hH : 0 < H) (hab : a ≤ b) (hlen : b - a ≤ X)
    (hband : ∀ t ∈ Icc a b, H ≤ |t|)
    (hF : Continuous F) (henergy : (∫ t in Icc a b, ‖F t‖ ^ 2) ≤ E) :
    (1 / X) * (∫ x in Icc X (2 * X),
      ‖transform F MellinSmoothingFunction.smoothing ε a b
        (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
      (32768 * Real.exp 2) * X ^ (2 : ℕ) * Real.log X * E / H ^ (2 : ℕ) := by
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  let σ := 1 + 1 / Real.log X
  have hσ : 1 ≤ σ := by
    dsimp [σ]
    have hh : 0 ≤ 1 / Real.log X := by positivity
    linarith
  have hσpos : 0 < σ := by linarith
  have hσtwo : σ ≤ 2 := by
    have hh : 1 / Real.log X ≤ 1 := (div_le_one (by linarith)).mpr hlog
    dsimp [σ]
    linarith
  have hδ : 0 ≤ Y / X := div_nonneg hY hXp.le
  have hδone : Y / X < 1 := (div_lt_one hXp).mpr hYX
  let g := fun t => F t * multiplier MellinSmoothingFunction.smoothing ε σ t *
    factor σ (Y / X) t
  have hg : Continuous g :=
    (hF.mul (continuous_multiplier MellinSmoothingFunction.smoothing ε σ hε hσpos
      MellinSmoothingFunction.differentiable MellinSmoothingFunction.nonnegative
      MellinSmoothingFunction.support MellinSmoothingFunction.mass_one)).mul
      (continuous_factor σ (Y / X) hσpos hδone)
  have hpoint : ∀ t ∈ Icc a b, ‖g t‖ ^ 2 ≤ (64 / H ^ (2 : ℕ)) * ‖F t‖ ^ 2 := by
    intro t ht
    have htpos : 0 < |t| := hH.trans_le (hband t ht)
    have hm := norm_le_four MellinSmoothingFunction.smoothing ε σ t hε hσpos hσtwo
      MellinSmoothingFunction.differentiable MellinSmoothingFunction.nonnegative
      MellinSmoothingFunction.support MellinSmoothingFunction.mass_one
    have hf : ‖factor σ (Y / X) t‖ ≤ 2 / H := by
      apply (norm_le_frequency σ (Y / X) t hσ hδ hδone (abs_pos.mp htpos)).trans
      exact div_le_div_of_nonneg_left (by norm_num) hH (hband t ht)
    have hnorm : ‖g t‖ ≤ ‖F t‖ * 4 * (2 / H) := by
      dsimp [g]
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hm (norm_nonneg _)) hf
        (norm_nonneg _) (by positivity)
    calc
      _ ≤ (‖F t‖ * 4 * (2 / H)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = _ := by ring
  have hgenergy : (∫ t in Icc a b, ‖g t‖ ^ 2) ≤ (64 / H ^ (2 : ℕ)) * E := by
    calc
      _ ≤ ∫ t in Icc a b, (64 / H ^ (2 : ℕ)) * ‖F t‖ ^ 2 := by
        apply integral_mono_ae (hg.norm.pow 2).integrableOn_Icc
          ((hF.norm.pow 2).const_mul _).integrableOn_Icc
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact hpoint t ht
      _ = (64 / H ^ (2 : ℕ)) * ∫ t in Icc a b, ‖F t‖ ^ 2 := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left henergy (by positivity)
  have heq : (∫ x in Icc X (2 * X),
      ‖transform F MellinSmoothingFunction.smoothing ε a b σ (Y / X) x‖ ^ 2) =
      ∫ x in Icc X (2 * X),
        ‖MellinIntegralMeanSquare.transform g a b σ x‖ ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change ‖transform F MellinSmoothingFunction.smoothing ε a b σ (Y / X) x‖ ^ 2 =
      ‖MellinIntegralMeanSquare.transform g a b σ x‖ ^ 2
    rw [SmoothedWindowTransfer.transform_eq F _ ε a b σ (Y / X) x hσpos,
      MellinWindowTransfer.transform_eq _ a b σ (Y / X) x
        (hXp.trans_le hx.1) hδone]
  rw [heq]
  apply (ShiftedMellinTransfer.mean_square_bound X a b hX hab hlen g hg).trans
  apply (mul_le_mul_of_nonneg_left hgenergy (by positivity)).trans_eq
  ring

theorem mean_square_bound (X Y ε H E : ℝ) (F : ℝ → ℂ)
    (hX : Real.exp 1 ≤ X) (hY : 0 ≤ Y) (hYX : Y < X)
    (hε : ε ∈ Ioo 0 1) (hH : 0 < H) (hHX : H ≤ X)
    (hF : Continuous F) (henergy : (∫ t in Icc H X, ‖F t‖ ^ 2) ≤ E) :
    (1 / X) * (∫ x in Icc X (2 * X),
      ‖transform F MellinSmoothingFunction.smoothing ε H X
        (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
      (32768 * Real.exp 2) * X ^ (2 : ℕ) * Real.log X * E / H ^ (2 : ℕ) := by
  exact separated_band_bound X Y ε H X H E F hX hY hYX hε hH hHX
    (by linarith) (fun t ht => ht.1.trans (le_abs_self t)) hF henergy

theorem negative_mean_square_bound (X Y ε H E : ℝ) (F : ℝ → ℂ)
    (hX : Real.exp 1 ≤ X) (hY : 0 ≤ Y) (hYX : Y < X)
    (hε : ε ∈ Ioo 0 1) (hH : 0 < H) (hHX : H ≤ X)
    (hF : Continuous F) (henergy : (∫ t in Icc (-X) (-H), ‖F t‖ ^ 2) ≤ E) :
    (1 / X) * (∫ x in Icc X (2 * X),
      ‖transform F MellinSmoothingFunction.smoothing ε (-X) (-H)
        (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
      (32768 * Real.exp 2) * X ^ (2 : ℕ) * Real.log X * E / H ^ (2 : ℕ) := by
  apply separated_band_bound X Y ε (-X) (-H) H E F hX hY hYX hε hH
    (by linarith) (by linarith) ?_ hF henergy
  intro t ht
  have hh := neg_le_abs t
  linarith [ht.2]

end SmoothedFrequencyTail

#print axioms SmoothedFrequencyTail.mean_square_bound
run_cmd do
  for target in [``SmoothedFrequencyTail.separated_band_bound,
      ``SmoothedFrequencyTail.mean_square_bound,
      ``SmoothedFrequencyTail.negative_mean_square_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "SMOOTHED FREQUENCY TAIL PASSED"
