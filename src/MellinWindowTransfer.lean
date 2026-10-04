import MellinWindowFactor

/-!
Mean-square transfer for the exact short-interval Mellin kernel.
The ratio delta is constant as x varies, as in Watt's y=xY/X convention.
This controls the integral; it does not identify a prime count with it.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set

namespace MellinWindowTransfer
open MellinWindowFactor

def transform (F : ℝ → ℂ) (a b σ δ x : ℝ) : ℂ :=
  ∫ t in Icc a b, F t *
    (((x : ℂ) ^ line σ t - ((x - x * δ : ℝ) : ℂ) ^ line σ t) / line σ t)

theorem power_difference (x σ δ t : ℝ) (hx : 0 < x) (hδ : δ < 1) :
    ((x : ℂ) ^ line σ t - ((x - x * δ : ℝ) : ℂ) ^ line σ t) / line σ t =
      factor σ δ t * (x : ℂ) ^ line σ t := by
  rw [show x - x * δ = x * (1 - δ) by ring, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hx.le (by linarith)]
  unfold factor
  ring

theorem transform_eq (F : ℝ → ℂ) (a b σ δ x : ℝ) (hx : 0 < x) (hδ : δ < 1) :
    transform F a b σ δ x =
      MellinIntegralMeanSquare.transform (fun t => F t * factor σ δ t) a b σ x := by
  unfold transform MellinIntegralMeanSquare.transform
  apply integral_congr_ae
  filter_upwards with t
  rw [power_difference x σ δ t hx hδ]
  unfold line
  ring

theorem mean_square_bound (X a b δ : ℝ) (hX : Real.exp 1 ≤ X)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ X) (hδ : 0 ≤ δ) (hδone : δ < 1)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (1 / X) * (∫ x in Icc X (2 * X),
      ‖transform F a b (1 + 1 / Real.log X) δ x‖ ^ 2) ≤
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
  let g := fun t => F t * factor σ δ t
  have hg : Continuous g := hF.mul (continuous_factor σ δ hσp hδone)
  have henergy : (∫ t in Icc a b, ‖g t‖ ^ 2) ≤ δ ^ 2 * ∫ t in Icc a b, ‖F t‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono (hg.norm.pow 2).integrableOn_Icc
      (by fun_prop : Continuous (fun t => δ ^ 2 * ‖F t‖ ^ 2)).integrableOn_Icc
    intro t
    dsimp [g]
    rw [norm_mul, mul_pow, mul_comm (δ ^ 2)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_le_width σ δ t hσ hδ hδone) 2)
      (sq_nonneg _)
  have htransform := HarmanMellinTransfer.mean_square_bound X a b hX ha hab hb g hg
  have heq : (∫ x in Icc X (2 * X), ‖transform F a b σ δ x‖ ^ 2) =
      ∫ x in Icc X (2 * X), ‖MellinIntegralMeanSquare.transform g a b σ x‖ ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change ‖transform F a b σ δ x‖ ^ 2 = ‖MellinIntegralMeanSquare.transform g a b σ x‖ ^ 2
    rw [transform_eq F a b σ δ x (hXp.trans_le hx.1) hδone]
  rw [heq]
  exact htransform.trans ((mul_le_mul_of_nonneg_left henergy (by positivity)).trans_eq (by ring))

theorem relative_window_bound (X Y a b : ℝ) (hX : Real.exp 1 ≤ X)
    (hY : 0 ≤ Y) (hYX : Y < X) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ X)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (1 / X) * (∫ x in Icc X (2 * X),
      ‖transform F a b (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
        (512 * Real.exp 2) * Y ^ 2 * Real.log X *
          ∫ t in Icc a b, ‖F t‖ ^ 2 := by
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hh := mean_square_bound X a b (Y / X) hX ha hab hb
    (div_nonneg hY hXp.le) ((div_lt_one hXp).mpr hYX) F hF
  apply hh.trans_eq
  field_simp

end MellinWindowTransfer

#print axioms MellinWindowTransfer.relative_window_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``MellinWindowTransfer.relative_window_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "MELLIN WINDOW TRANSFER PASSED"
