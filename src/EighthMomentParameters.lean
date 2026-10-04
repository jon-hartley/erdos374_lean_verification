import FlatEighthMoment

/-!
Exact coefficient formulas and uniform logarithm comparisons for the
eighth-moment application. No asymptotic factor is suppressed.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace EighthMomentParameters
open NormalizedPowerLevel DyadicLevelParameters

def quadraticConstant : ℝ := 516 * 3 ^ 3 * 8
def sexticConstant : ℝ := 516 * 1024 ^ 2 * 3 ^ 7 * 8

theorem quadratic_eq (D : ℝ) (N : ℕ) (T ε : ℝ) (hN : 1 ≤ N) :
    quadratic (N ^ 3) 3 T (energyBudget D N 3 ε 1) =
      quadraticConstant * D * (2 * (N : ℝ)) ^ ε * (1 + Real.log (T + 1)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold quadratic energyBudget quadraticConstant
  push_cast
  field_simp

theorem sextic_eq (D : ℝ) (N : ℕ) (T ε : ℝ) (hN : 1 ≤ N) :
    sextic (N ^ 3) 3 T (energyBudget D N 3 ε 1) =
      sexticConstant * D ^ 3 * ((2 * (N : ℝ)) ^ ε) ^ 3 *
        (1 + Real.log (T + 1)) * (1 + Real.log (8 * (N : ℝ) ^ 3 + 1)) * T / (N : ℝ) ^ 6 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold sextic energyBudget sexticConstant
  push_cast
  norm_num only [show (2 : ℝ) ^ 3 = 8 by norm_num]
  field_simp
  ring

theorem log_bounds (N T X : ℝ) (hN : 1 ≤ N) (hNX : N ≤ X)
    (hT : 1 ≤ T) (hTX : T ≤ X) :
    1 ≤ 1 + Real.log X ∧
      Real.log (2 * N) ≤ 1 + Real.log X ∧
      1 + Real.log (T + 1) ≤ 2 * (1 + Real.log X) ∧
      1 + Real.log (8 * N ^ 3 + 1) ≤ 5 * (1 + Real.log X) := by
  have hX : 1 ≤ X := hN.trans hNX
  have hXp : 0 < X := by linarith
  have hNp : 0 < N := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hl2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlog2X : Real.log (2 * X) ≤ 1 + Real.log X := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXp.ne']
    linarith
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · exact (Real.log_le_log (by positivity : 0 < 2 * N) (by linarith)).trans hlog2X
  · have hh := (Real.log_le_log (by linarith : 0 < T + 1)
      (show T + 1 ≤ 2 * X by linarith)).trans hlog2X
    linarith
  · have hN3 : N ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hNp.le hNX 3
    have hX34 : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX (by norm_num)
    have hX4 : 1 ≤ X ^ 4 := one_le_pow₀ hX
    have hh := Real.log_le_log (by positivity : 0 < 8 * N ^ 3 + 1)
      (show 8 * N ^ 3 + 1 ≤ (2 * X) ^ 4 by nlinarith)
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith

end EighthMomentParameters

#print axioms EighthMomentParameters.log_bounds
run_cmd do
  for decl in [``EighthMomentParameters.quadratic_eq, ``EighthMomentParameters.sextic_eq,
      ``EighthMomentParameters.log_bounds] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "EIGHTH MOMENT PARAMETERS PASSED"
