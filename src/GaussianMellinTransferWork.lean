import GaussianFourierIntegralWork
import SmoothedWindowTransfer

/-! Lossless Mellin/window square-mean transfer. There is no frequency
length restriction and no logarithmic loss in this integral estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
namespace GaussianMellinTransferWork
open MellinIntegralMeanSquare MellinWindowFactor
theorem endpoint_bound (X σ a b : ℝ) (hX : 0 < X) (hσ : 0 ≤ σ)
    (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ x in Icc X (2 * X), ‖transform g a b σ x‖ ^ 2) ≤
      (2 * X) ^ (2 * σ + 1) * (Real.exp 1 * GaussianFourierIntegralWork.rowConstant) *
        ∫ t in Icc a b, ‖g t‖ ^ 2 := by
  let F := CompactIntegral.transform FourierIntegralMeanSquare.kernel g a b
  have hF : Continuous F := CompactIntegral.continuous_transform
    FourierIntegralMeanSquare.kernel g a b FourierIntegralMeanSquare.continuous_kernel hg
  have hXY : X ≤ 2 * X := by linarith
  have hlogs : Real.log X ≤ Real.log (2 * X) := Real.log_le_log hX hXY
  have hlen : Real.log (2 * X) - Real.log X ≤ 1 := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX.ne']
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc
    _ = ∫ x in Icc X (2 * X), x ^ (2 * σ) * ‖F (Real.log x)‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact norm_square g a b σ x (hX.trans_le hx.1)
    _ ≤ (2 * X) ^ (2 * σ + 1) *
        ∫ v in Icc (Real.log X) (Real.log (2 * X)), ‖F v‖ ^ 2 :=
      LogIntegralTransfer.weighted_bound X (2 * X) σ hX hXY hσ F hF
    _ ≤ (2 * X) ^ (2 * σ + 1) *
        ((Real.exp 1 * GaussianFourierIntegralWork.rowConstant) * ∫ t in Icc a b, ‖g t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (GaussianFourierIntegralWork.mean_square_bound a b (Real.log X)
          (Real.log (2 * X)) hlogs hlen g hg) (by positivity)
    _ = _ := by ring

def transferConstant : ℝ :=
  32 * Real.exp 2 * (Real.exp 1 * GaussianFourierIntegralWork.rowConstant)

theorem transferConstant_pos : 0<transferConstant := by
  unfold transferConstant GaussianFourierIntegralWork.rowConstant
  positivity

theorem mean_square_bound (X a b : ℝ) (hX : Real.exp 1≤X)
    (g : ℝ → ℂ) (hg : Continuous g) :
    (1/X) * (∫ x in Icc X (2*X),
      ‖MellinIntegralMeanSquare.transform g a b (1+1/Real.log X) x‖^2) ≤
        transferConstant * X^2 * (∫ t in Icc a b, ‖g t‖^2) := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hlog : 1≤Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hh := endpoint_bound X (1+1/Real.log X) a b hXp (by positivity) g hg
  have hfactor := HarmanMellinTransfer.endpoint_factor X hX
  have he : 0≤Real.exp 1 * GaussianFourierIntegralWork.rowConstant := by
    unfold GaussianFourierIntegralWork.rowConstant
    positivity
  have henergy : 0≤∫ t in Icc a b, ‖g t‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have htotal := hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfactor he) henergy)
  apply (mul_le_mul_of_nonneg_left htotal (by positivity : 0≤1/X)).trans_eq
  unfold transferConstant
  field_simp

theorem window_bound (X a b δ : ℝ) (hX : Real.exp 1 ≤ X)
    (hδ : 0 ≤ δ) (hδone : δ < 1)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (1 / X) * (∫ x in Icc X (2 * X),
      ‖MellinWindowTransfer.transform F a b (1 + 1 / Real.log X) δ x‖ ^ 2) ≤
        transferConstant * X ^ 2 * δ ^ 2 *
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
  have htransform := mean_square_bound X a b hX g hg
  have heq : (∫ x in Icc X (2 * X), ‖MellinWindowTransfer.transform F a b σ δ x‖ ^ 2) =
      ∫ x in Icc X (2 * X), ‖MellinIntegralMeanSquare.transform g a b σ x‖ ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change ‖MellinWindowTransfer.transform F a b σ δ x‖ ^ 2 = ‖MellinIntegralMeanSquare.transform g a b σ x‖ ^ 2
    rw [MellinWindowTransfer.transform_eq F a b σ δ x (hXp.trans_le hx.1) hδone]
  rw [heq]
  exact htransform.trans ((mul_le_mul_of_nonneg_left henergy (mul_nonneg transferConstant_pos.le (sq_nonneg X))).trans_eq (by ring))

theorem relative_window_bound (X Y a b : ℝ) (hX : Real.exp 1 ≤ X)
    (hY : 0 ≤ Y) (hYX : Y < X)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (1 / X) * (∫ x in Icc X (2 * X),
      ‖MellinWindowTransfer.transform F a b (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
        transferConstant * Y ^ 2 *
          ∫ t in Icc a b, ‖F t‖ ^ 2 := by
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hh := window_bound X a b (Y / X) hX
    (div_nonneg hY hXp.le) ((div_lt_one hXp).mpr hYX) F hF
  apply hh.trans_eq
  field_simp

open SmoothMellinMultiplier

theorem smoothed_window_bound (Ψ : ℝ → ℝ) (hdiff : ContDiff ℝ 1 Ψ)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ Ψ x) (hmass : ∫ x in Ioi 0, Ψ x / x = 1)
    (X Y ε a b : ℝ) (hX : Real.exp 1 ≤ X) (hY : 0 ≤ Y) (hYX : Y < X)
    (hε : ε ∈ Ioo 0 1)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (1 / X) * (∫ x in Icc X (2 * X),
      ‖SmoothedWindowTransfer.transform F Ψ ε a b (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
        (16 * transferConstant) * Y ^ 2 * ∫ t in Icc a b, ‖F t‖ ^ 2 := by
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  let σ := 1 + 1 / Real.log X
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσtwo : σ ≤ 2 := by
    have hh : 1 / Real.log X ≤ 1 := (div_le_one (by linarith)).mpr hlog
    dsimp [σ]
    linarith
  let g := fun t => F t * multiplier Ψ ε σ t
  have hg : Continuous g := hF.mul (continuous_multiplier Ψ ε σ hε hσ hdiff hnonneg hsupport hmass)
  have henergy : (∫ t in Icc a b, ‖g t‖ ^ 2) ≤ 16 * ∫ t in Icc a b, ‖F t‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono (hg.norm.pow 2).integrableOn_Icc
      (by fun_prop : Continuous (fun t => 16 * ‖F t‖ ^ 2)).integrableOn_Icc
    intro t
    dsimp [g]
    rw [norm_mul, mul_pow, mul_comm (16 : ℝ)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have hh := pow_le_pow_left₀ (norm_nonneg _)
      (norm_le_four Ψ ε σ t hε hσ hσtwo hdiff hnonneg hsupport hmass) 2
    norm_num at hh ⊢
    exact hh
  have hwindow := window_bound X a b (Y / X) hX
    (div_nonneg hY hXp.le) ((div_lt_one hXp).mpr hYX) g hg
  have heq : (∫ x in Icc X (2 * X), ‖SmoothedWindowTransfer.transform F Ψ ε a b σ (Y / X) x‖ ^ 2) =
      ∫ x in Icc X (2 * X), ‖MellinWindowTransfer.transform g a b σ (Y / X) x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    rw [SmoothedWindowTransfer.transform_eq F Ψ ε a b σ (Y / X) x hσ]
  rw [heq]
  apply hwindow.trans
  apply (mul_le_mul_of_nonneg_left henergy (mul_nonneg
    (mul_nonneg transferConstant_pos.le (sq_nonneg X)) (sq_nonneg (Y/X)))).trans_eq
  field_simp

#print axioms relative_window_bound
run_cmd do
  for decl in [``endpoint_bound, ``transferConstant_pos, ``mean_square_bound,
      ``window_bound, ``relative_window_bound, ``smoothed_window_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end GaussianMellinTransferWork
