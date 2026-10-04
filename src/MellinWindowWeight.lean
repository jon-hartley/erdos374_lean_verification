import MellinWindowFactor

/-!
The exact window factor has both a short-width bound and frequency decay.
Retaining the smaller bound gives the weighted Mellin transfer used for
high-frequency pieces of the short-interval argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set

namespace MellinWindowWeight
open MellinWindowFactor

def weight (σ δ t : ℝ) : ℝ := min (δ ^ 2) (4 / (σ ^ 2 + t ^ 2))

theorem norm_line_square (σ t : ℝ) : ‖line σ t‖ ^ 2 = σ ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [line, sq]

theorem weight_nonnegative (σ δ t : ℝ) : 0 ≤ weight σ δ t := by
  unfold weight
  positivity

theorem continuous_weight (σ δ : ℝ) (hσ : 0 < σ) : Continuous (weight σ δ) := by
  unfold weight
  apply continuous_const.min
  apply Continuous.div continuous_const (by fun_prop)
  intro t
  exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hσ) (sq_nonneg t))

theorem norm_square_le_weight (σ δ t : ℝ) (hσ : 1 ≤ σ)
    (hδ : 0 ≤ δ) (hδone : δ < 1) :
    ‖factor σ δ t‖ ^ 2 ≤ weight σ δ t := by
  apply le_min
  · exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_width σ δ t hσ hδ hδone) 2
  · have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_le_line σ δ t hσ hδ hδone) 2
    simpa only [div_pow, norm_line_square, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh

theorem mean_square_bound (X a b δ : ℝ) (hX : Real.exp 1 ≤ X)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ X) (hδ : 0 ≤ δ) (hδone : δ < 1)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (1 / X) * (∫ x in Icc X (2 * X),
      ‖MellinIntegralMeanSquare.transform
        (fun t => F t * factor (1 + 1 / Real.log X) δ t)
        a b (1 + 1 / Real.log X) x‖ ^ 2) ≤
        (512 * Real.exp 2) * X ^ 2 * Real.log X *
          ∫ t in Icc a b, weight (1 + 1 / Real.log X) δ t * ‖F t‖ ^ 2 := by
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  let σ := 1 + 1 / Real.log X
  have hσ : 1 ≤ σ := by
    have hh : 0 ≤ 1 / Real.log X := by positivity
    dsimp [σ]
    linarith
  have hσp : 0 < σ := by linarith
  let g := fun t => F t * factor σ δ t
  have hg : Continuous g := hF.mul (continuous_factor σ δ hσp hδone)
  apply (HarmanMellinTransfer.mean_square_bound X a b hX ha hab hb g hg).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (hg.norm.pow 2).integrableOn_Icc
    ((continuous_weight σ δ hσp).mul (hF.norm.pow 2)).integrableOn_Icc
  intro t
  dsimp [g]
  rw [norm_mul, mul_pow, mul_comm (weight σ δ t)]
  exact mul_le_mul_of_nonneg_left (norm_square_le_weight σ δ t hσ hδ hδone) (sq_nonneg _)

end MellinWindowWeight

#print axioms MellinWindowWeight.mean_square_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``MellinWindowWeight.mean_square_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "MELLIN WINDOW WEIGHT PASSED"
