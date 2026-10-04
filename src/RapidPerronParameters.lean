import RapidSmoothedPerron
import PolynomialLogEnvelope

/-!
Concrete error parameters: epsilon=X^(-19/20), T=X and k=20.
The boundary has exponent at most 1/100+1/20=3/50.
The tail has exponent at most 1/100+1-21/20=-1/25.
Fixed constants are absorbed to give error <=X^(2/25).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter

namespace RapidPerronParameters

theorem width_power (X : ℝ) (hX : 0 < X) :
    X ^ (-19 / 20 : ℝ) * X = X ^ (1 / 20 : ℝ) := by
  calc
    _ = X ^ (-19 / 20 : ℝ) * X ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hX]; congr 1; norm_num

theorem vertical_power (X : ℝ) (hX : 0 < X) (hlog : Real.log X ≠ 0) :
    X ^ (1 + 1 / Real.log X) = X * Real.exp 1 := by
  rw [Real.rpow_add hX, Real.rpow_one]
  congr 1
  rw [Real.rpow_def_of_pos hX]
  congr 1
  field_simp

theorem eventual_error (C : ℝ) (hC : 0 < C) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ M W : ℝ, 0 ≤ M → M ≤ X ^ (1 / 100 : ℝ) → 0 ≤ W → W ≤ X ^ (1 / 100 : ℝ) →
      W * (4 * Real.log 2 * X ^ (-19 / 20 : ℝ) * X + 1) +
        (1 / (2 * Real.pi)) *
          (2 * M * C * X ^ (1 + 1 / Real.log X) /
            (21 * (X ^ (-19 / 20 : ℝ) * X) ^ (21 : ℕ))) ≤ X ^ (2 / 25 : ℝ) := by
  let D := 4 * Real.log 2 + 1 + 2 * C * Real.exp 1
  have hlogtwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  filter_upwards [PolynomialLogEnvelope.eventually_bound D 0 (1 / 50) hD (by norm_num),
    eventually_ge_atTop (Real.exp 1)] with X hX hlarge
  refine ⟨hlarge, ?_⟩
  intro M W hM hMbound hW hWbound
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hlarge
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hlarge
  have hwidth := width_power X hXp
  have hwidthone : 1 ≤ X ^ (1 / 20 : ℝ) := Real.one_le_rpow hX.1 (by norm_num)
  have hwidthpower : (X ^ (-19 / 20 : ℝ) * X) ^ (21 : ℕ) = X ^ (21 / 20 : ℝ) := by
    rw [hwidth, ← Real.rpow_mul_natCast hXp.le]
    congr 1
    norm_num
  have hproduct : X ^ (1 / 100 : ℝ) * X ^ (1 / 20 : ℝ) = X ^ (3 / 50 : ℝ) := by
    rw [← Real.rpow_add hXp]
    congr 1
    norm_num
  have hratio : X ^ (1 / 100 : ℝ) * X / X ^ (21 / 20 : ℝ) = X ^ (-1 / 25 : ℝ) := by
    calc
      _ = (X ^ (1 / 100 : ℝ) * X ^ (1 : ℝ)) / X ^ (21 / 20 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hXp, ← Real.rpow_sub hXp]
        congr 1
        norm_num
  have hboundary : W * (4 * Real.log 2 * X ^ (-19 / 20 : ℝ) * X + 1) ≤
      (4 * Real.log 2 + 1) * X ^ (3 / 50 : ℝ) := by
    calc
      _ = W * (4 * Real.log 2 * X ^ (1 / 20 : ℝ) + 1) := by rw [← hwidth]; ring
      _ ≤ X ^ (1 / 100 : ℝ) * (4 * Real.log 2 * X ^ (1 / 20 : ℝ) + X ^ (1 / 20 : ℝ)) := by
        gcongr
      _ = (4 * Real.log 2 + 1) * (X ^ (1 / 100 : ℝ) * X ^ (1 / 20 : ℝ)) := by ring
      _ = _ := by rw [hproduct]
  have hpi : 1 / (2 * Real.pi) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Real.pi_gt_three])
  have htail : (1 / (2 * Real.pi)) *
      (2 * M * C * X ^ (1 + 1 / Real.log X) /
        (21 * (X ^ (-19 / 20 : ℝ) * X) ^ (21 : ℕ))) ≤
      (2 * C * Real.exp 1) * X ^ (-1 / 25 : ℝ) := by
    rw [hwidthpower, vertical_power X hXp (by linarith)]
    calc
      _ ≤ 2 * M * C * (X * Real.exp 1) / (21 * X ^ (21 / 20 : ℝ)) :=
        mul_le_of_le_one_left (by positivity) hpi
      _ ≤ 2 * M * C * (X * Real.exp 1) / X ^ (21 / 20 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [Real.rpow_pos_of_pos hXp (21 / 20 : ℝ)])
      _ ≤ 2 * X ^ (1 / 100 : ℝ) * C * (X * Real.exp 1) / X ^ (21 / 20 : ℝ) := by gcongr
      _ = (2 * C * Real.exp 1) * (X ^ (1 / 100 : ℝ) * X / X ^ (21 / 20 : ℝ)) := by ring
      _ = _ := by rw [hratio]
  calc
    _ ≤ (4 * Real.log 2 + 1) * X ^ (3 / 50 : ℝ) + (2 * C * Real.exp 1) * X ^ (-1 / 25 : ℝ) :=
      add_le_add hboundary htail
    _ ≤ (4 * Real.log 2 + 1) * X ^ (3 / 50 : ℝ) + (2 * C * Real.exp 1) * X ^ (3 / 50 : ℝ) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX.1 (by norm_num : (-1 / 25 : ℝ) ≤ 3 / 50))
        (by positivity : 0 ≤ 2 * C * Real.exp 1))
    _ = D * X ^ (3 / 50 : ℝ) := by dsimp [D]; ring
    _ ≤ X ^ (1 / 50 : ℝ) * X ^ (3 / 50 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [pow_zero, mul_one] using hX.2
    _ = _ := by rw [← Real.rpow_add hXp]; congr 1; norm_num

end RapidPerronParameters

#print axioms RapidPerronParameters.eventual_error
run_cmd do
  let axioms ← Lean.collectAxioms ``RapidPerronParameters.eventual_error
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "RAPID PERRON PARAMETERS PASSED"
