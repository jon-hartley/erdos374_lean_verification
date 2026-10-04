import EighthMomentParameters

/-!
Uniform ambient-scale envelopes for the explicit eighth-moment inputs.
The polynomial length and time are at most X; all constants remain fixed.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace TripleAdoptEighthParameterEnvelope
open EighthMomentParameters NormalizedPowerLevel DyadicLevelParameters FlatEighthMoment

def quadraticFactor (D α : ℝ) : ℝ := 2 * quadraticConstant * D * (2 : ℝ) ^ α
def sexticFactor (D α : ℝ) : ℝ := 10 * sexticConstant * D ^ 3 * ((2 : ℝ) ^ α) ^ 3
def meanFactor (C α : ℝ) : ℝ := 128 * C * (2 : ℝ) ^ α

theorem parameter_bounds (D C : ℝ) (N : ℕ) (T X α : ℝ)
    (hD : 0 < D) (hC : 0 < C) (hN : 1 ≤ N) (hNX : (N : ℝ) ≤ X)
    (hT : 1 ≤ T) (hTX : T ≤ X) (hα : 0 ≤ α) :
    quadratic (N ^ 3) 3 T (energyBudget D N 3 α 1) ≤
      quadraticFactor D α * X ^ α * (1 + Real.log X) ∧
    sextic (N ^ 3) 3 T (energyBudget D N 3 α 1) ≤
      sexticFactor D α * (X ^ α) ^ 3 * (1 + Real.log X) ^ 2 * T / (N : ℝ) ^ 6 ∧
    meanSix C N T α ≤
      meanFactor C α * X ^ α * (1 + Real.log X) * (1 + T / (N : ℝ) ^ 3) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hX : 1 ≤ X := hNR.trans hNX
  have hXp : 0 < X := by linarith
  have hlogs := log_bounds N T X hNR hNX hT hTX
  have hpow : (2 * (N : ℝ)) ^ α ≤ (2 : ℝ) ^ α * X ^ α := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hNp.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hNp.le hNX hα) (by positivity)
  have hGT : 0 ≤ 1 + Real.log (T + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
    linarith
  have hGN : 0 ≤ 1 + Real.log (8 * (N : ℝ) ^ 3 + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ 8 * (N : ℝ) ^ 3 + 1 by
      have hh : 0 ≤ (N : ℝ) ^ 3 := by positivity
      linarith)
    linarith
  have hGX : 0 ≤ 1 + Real.log X := by linarith [hlogs.1]
  have hq : 0 ≤ quadraticConstant := by norm_num [quadraticConstant]
  have hb : 0 ≤ sexticConstant := by norm_num [sexticConstant]
  refine ⟨?_, ?_, ?_⟩
  · rw [quadratic_eq D N T α hN]
    calc
      _ ≤ quadraticConstant * D * ((2 : ℝ) ^ α * X ^ α) * (2 * (1 + Real.log X)) := by
        gcongr
        exact hlogs.2.2.1
      _ = _ := by unfold quadraticFactor; ring
  · rw [sextic_eq D N T α hN]
    calc
      _ ≤ sexticConstant * D ^ 3 * ((2 : ℝ) ^ α * X ^ α) ^ 3 *
          (2 * (1 + Real.log X)) * (5 * (1 + Real.log X)) * T / (N : ℝ) ^ 6 := by
        gcongr
        · exact hlogs.2.2.1
        · exact hlogs.2.2.2
      _ = _ := by unfold sexticFactor; ring
  · unfold meanSix
    have hbracket : T / (N : ℝ) ^ 3 + 32 * (1 + 3 * Real.log (2 * N)) ≤
        128 * (1 + Real.log X) * (1 + T / (N : ℝ) ^ 3) := by
      have hratio : 0 ≤ T / (N : ℝ) ^ 3 := by positivity
      nlinarith [hlogs.2.1, mul_nonneg hratio (show 0 ≤ Real.log X by
        linarith [hlogs.1])]
    have hbracket0 : 0 ≤ T / (N : ℝ) ^ 3 + 32 * (1 + 3 * Real.log (2 * N)) := by
      have hh := Real.log_nonneg (show 1 ≤ 2 * (N : ℝ) by linarith)
      positivity
    calc
      _ ≤ C * ((2 : ℝ) ^ α * X ^ α) *
          (128 * (1 + Real.log X) * (1 + T / (N : ℝ) ^ 3)) := by
        gcongr
      _ = _ := by unfold meanFactor; ring

theorem sextic_lower (D : ℝ) (N : ℕ) (T X α : ℝ)
    (hD : 0 < D) (hN : 1 ≤ N) (hNX : (N : ℝ) ≤ X)
    (hT : 1 ≤ T) (hα : 0 ≤ α) :
    sexticConstant * D ^ 3 / X ^ 6 ≤
      sextic (N ^ 3) 3 T (energyBudget D N 3 α 1) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hp : 1 ≤ (2 * (N : ℝ)) ^ α := Real.one_le_rpow (by linarith) hα
  have hGT : 1 ≤ 1 + Real.log (T + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
    linarith
  have hGN : 1 ≤ 1 + Real.log (8 * (N : ℝ) ^ 3 + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ 8 * (N : ℝ) ^ 3 + 1 by
      have hh : 0 ≤ (N : ℝ) ^ 3 := by positivity
      linarith)
    linarith
  have hb : 0 ≤ sexticConstant := by norm_num [sexticConstant]
  rw [sextic_eq D N T α hN]
  calc
    _ ≤ sexticConstant * D ^ 3 / (N : ℝ) ^ 6 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hNp.le hNX 6)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        sexticConstant * D ^ 3 = sexticConstant * D ^ 3 * 1 ^ 3 * 1 * 1 * 1 := by ring
        _ ≤ _ := by gcongr

end TripleAdoptEighthParameterEnvelope

#print axioms TripleAdoptEighthParameterEnvelope.parameter_bounds
run_cmd do
  for decl in [``TripleAdoptEighthParameterEnvelope.parameter_bounds, ``TripleAdoptEighthParameterEnvelope.sextic_lower] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "EIGHTH PARAMETER ENVELOPE PASSED"
