import MellinWindowTransfer

/-!
The mean-square transfer depends on the length of the frequency interval,
not its location. This version permits negative frequency intervals and
retains the same normalized spatial range and constant.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace ShiftedMellinTransfer

theorem mean_square_bound (X a b : ℝ) (hX : Real.exp 1 ≤ X)
    (hab : a ≤ b) (hlen : b - a ≤ X) (g : ℝ → ℂ) (hg : Continuous g) :
    (1 / X) * (∫ x in Icc X (2 * X),
      ‖MellinIntegralMeanSquare.transform g a b (1 + 1 / Real.log X) x‖ ^ 2) ≤
        (512 * Real.exp 2) * X ^ 2 * Real.log X *
          ∫ t in Icc a b, ‖g t‖ ^ 2 := by
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hσ : 0 ≤ 1 + 1 / Real.log X := by positivity
  have hinput : 0 ≤ ∫ t in Icc a b, ‖g t‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hlogarg : 0 ≤ Real.log (1 + b - a) := Real.log_nonneg (by linarith)
  have hlogfactor : Real.log (1 + b - a) ≤ 2 * Real.log X := by
    simpa only [sub_zero, add_sub_assoc] using HarmanMellinTransfer.logarithmic_factor X 0 (b - a)
      hX (by norm_num) (by linarith) hlen
  have hfirst := MellinIntegralMeanSquare.endpoint_bound X
    (1 + 1 / Real.log X) a b hXp hσ g hg
  have hfactor := mul_le_mul (HarmanMellinTransfer.endpoint_factor X hX)
    (mul_le_mul_of_nonneg_left hlogfactor (by norm_num : (0 : ℝ) ≤ 8))
    (by positivity) (by positivity)
  have htotal := hfirst.trans (mul_le_mul_of_nonneg_right hfactor hinput)
  have hnormalized := mul_le_mul_of_nonneg_left htotal (le_of_lt (one_div_pos.mpr hXp))
  calc
    _ ≤ (1 / X) *
        ((32 * Real.exp 2 * X ^ 3) * (8 * (2 * Real.log X)) *
          ∫ t in Icc a b, ‖g t‖ ^ 2) := hnormalized
    _ = _ := by field_simp; ring

theorem window_bound (X a b δ : ℝ) (hX : Real.exp 1 ≤ X)
    (hab : a ≤ b) (hlen : b - a ≤ X) (hδ : 0 ≤ δ) (hδone : δ < 1)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (1 / X) * (∫ x in Icc X (2 * X),
      ‖MellinWindowTransfer.transform F a b (1 + 1 / Real.log X) δ x‖ ^ 2) ≤
        (512 * Real.exp 2) * X ^ 2 * Real.log X * δ ^ 2 *
          ∫ t in Icc a b, ‖F t‖ ^ 2 := by
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  let σ := 1 + 1 / Real.log X
  have hσ : 1 ≤ σ := by
    have hinv : 0 ≤ 1 / Real.log X := by positivity
    dsimp [σ]
    linarith
  have hσp : 0 < σ := by linarith
  let g := fun t => F t * MellinWindowFactor.factor σ δ t
  have hg : Continuous g := hF.mul (MellinWindowFactor.continuous_factor σ δ hσp hδone)
  have henergy : (∫ t in Icc a b, ‖g t‖ ^ 2) ≤ δ ^ 2 * ∫ t in Icc a b, ‖F t‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono (hg.norm.pow 2).integrableOn_Icc
      (by fun_prop : Continuous (fun t => δ ^ 2 * ‖F t‖ ^ 2)).integrableOn_Icc
    intro t
    dsimp [g]
    rw [norm_mul, mul_pow, mul_comm (δ ^ 2)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _)
        (MellinWindowFactor.norm_le_width σ δ t hσ hδ hδone) 2) (sq_nonneg _)
  have htransform := mean_square_bound X a b hX hab hlen g hg
  have heq : (∫ x in Icc X (2 * X), ‖MellinWindowTransfer.transform F a b σ δ x‖ ^ 2) =
      ∫ x in Icc X (2 * X), ‖MellinIntegralMeanSquare.transform g a b σ x‖ ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change ‖MellinWindowTransfer.transform F a b σ δ x‖ ^ 2 =
      ‖MellinIntegralMeanSquare.transform g a b σ x‖ ^ 2
    rw [MellinWindowTransfer.transform_eq F a b σ δ x (hXp.trans_le hx.1) hδone]
  rw [heq]
  exact htransform.trans ((mul_le_mul_of_nonneg_left henergy (by positivity)).trans_eq (by ring))

end ShiftedMellinTransfer

#print axioms ShiftedMellinTransfer.window_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``ShiftedMellinTransfer.window_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "SHIFTED MELLIN TRANSFER PASSED"
