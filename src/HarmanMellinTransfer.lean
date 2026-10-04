import MellinIntegralMeanSquare

/-!
The explicit X² log X mean-square transfer, with the vertical line
at sigma = 1 + 1/log X. The integral is parameterized by its imaginary
coordinate t; multiplication by i for the contour differential does
not alter the squared norm.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set

namespace HarmanMellinTransfer

theorem endpoint_factor (X : ℝ) (hX : Real.exp 1 ≤ X) :
    (2 * X) ^ (2 * (1 + 1 / Real.log X) + 1) ≤
      32 * Real.exp 2 * X ^ 3 := by
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hlogp : 0 < Real.log X := by linarith
  have hinv : 1 / Real.log X ≤ 1 := (div_le_one hlogp).mpr hlog
  have htwo : (2 : ℝ) ^ (2 * (1 + 1 / Real.log X) + 1) ≤ 32 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show 2 * (1 + 1 / Real.log X) + 1 ≤ (5 : ℝ) by linarith)
    norm_num at hh ⊢
    exact hh
  have hpow : X ^ (2 * (1 + 1 / Real.log X) + 1) = X ^ 3 * Real.exp 2 := by
    rw [show 2 * (1 + 1 / Real.log X) + 1 = 3 + 2 / Real.log X by ring,
      Real.rpow_add hXp]
    have hexp : X ^ (2 / Real.log X) = Real.exp 2 := by
      rw [Real.rpow_def_of_pos hXp]
      congr 1
      field_simp
    rw [hexp]
    norm_num
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hXp.le, hpow]
  have hh := mul_le_mul_of_nonneg_right htwo
    (by positivity : 0 ≤ X ^ 3 * Real.exp 2)
  nlinarith

theorem logarithmic_factor (X a b : ℝ) (hX : Real.exp 1 ≤ X)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ X) :
    Real.log (1 + b - a) ≤ 2 * Real.log X := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hXtwo : 2 ≤ X := htwo.trans hX
  have hXp : 0 < X := by linarith
  have harg : 0 < 1 + b - a := by linarith
  have hh := Real.log_le_log harg (show 1 + b - a ≤ 2 * X by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXp.ne'] at hh
  have htwoLog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hXtwo
  linarith

theorem mean_square_bound (X a b : ℝ) (hX : Real.exp 1 ≤ X)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ X)
    (g : ℝ → ℂ) (hg : Continuous g) :
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
  have hfirst := MellinIntegralMeanSquare.endpoint_bound X
    (1 + 1 / Real.log X) a b hXp hσ g hg
  have hfactor := mul_le_mul (endpoint_factor X hX)
    (mul_le_mul_of_nonneg_left (logarithmic_factor X a b hX ha hab hb)
      (by norm_num : (0 : ℝ) ≤ 8)) (by positivity) (by positivity)
  have htotal := hfirst.trans (mul_le_mul_of_nonneg_right hfactor hinput)
  have hnormalized := mul_le_mul_of_nonneg_left htotal (le_of_lt (one_div_pos.mpr hXp))
  calc
    _ ≤ (1 / X) *
        ((32 * Real.exp 2 * X ^ 3) * (8 * (2 * Real.log X)) *
          ∫ t in Icc a b, ‖g t‖ ^ 2) := hnormalized
    _ = _ := by field_simp; ring

end HarmanMellinTransfer

#print axioms HarmanMellinTransfer.mean_square_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``HarmanMellinTransfer.mean_square_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "HARMAN MELLIN TRANSFER PASSED"
