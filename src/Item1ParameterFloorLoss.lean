import Item1ParameterChoice
import Item1ParameterGainBasic

/-! The explicit cost of replacing the averaging scale by its integer floor. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Item1ParameterFloorLoss
open Item1ParameterCore

theorem etaLoss_nonneg (d : ℕ) (hd : 1 ≤ d) : 0 ≤ etaLoss d := by
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdp : (0:ℝ) < (d:ℝ) := by linarith
  have hb : 0 ≤ 1-1/(d:ℝ) := by
    have h := (div_le_one hdp).mpr hd1
    linarith
  unfold etaLoss
  positivity

theorem remaining_exponent_bounds (d : ℕ) (hd : 1 ≤ d) :
    -(d:ℝ)*((d:ℝ)+1) ≤ -(d:ℝ)*((d:ℝ)+1)+3*etaLoss d ∧
    -(d:ℝ)*((d:ℝ)+1)+3*etaLoss d ≤ 0 := by
  have hn := etaLoss_nonneg d hd
  have hu := Item1ParameterGain.etaLoss_le d hd
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
  constructor <;> nlinarith [sq_nonneg (d:ℝ)]

theorem floor_power_loss (M A D e : ℝ) (hM : 0 < M)
    (hA : M^(1/3:ℝ)/2 ≤ A) (he : -D ≤ e) (he0 : e ≤ 0) :
    A^e ≤ Real.exp (D*Real.log 2+(e/3)*Real.log M) := by
  calc
    A^e ≤ (M^(1/3:ℝ)/2)^e :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hA he0
    _ = M^(e/3)*(2:ℝ)^(-e) := by
      rw [Real.div_rpow (Real.rpow_nonneg hM.le _) (by norm_num),
        ← Real.rpow_mul hM.le, div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        show (1/3:ℝ)*e=e/3 by ring]
    _ ≤ M^(e/3)*(2:ℝ)^D :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
        (Real.rpow_nonneg hM.le _)
    _ = Real.exp (D*Real.log 2+(e/3)*Real.log M) := by
      rw [Real.rpow_def_of_pos hM, Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
        ← Real.exp_add]
      congr 1
      ring

end Item1ParameterFloorLoss

run_cmd do
  for target in [``Item1ParameterFloorLoss.etaLoss_nonneg,
      ``Item1ParameterFloorLoss.remaining_exponent_bounds,
      ``Item1ParameterFloorLoss.floor_power_loss] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER FLOOR LOSS: 3 standard-axiom theorem guards passed."
