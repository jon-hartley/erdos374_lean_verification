import ProductMomentParameters

/-!
Ambient-scale envelopes for the mixed-product moment coefficients.
The two individual lengths are at most X, so their product is at most X².
All constants and both coefficient losses are retained explicitly.
-/

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section

namespace ProductParameterEnvelope
open ProductMomentParameters DyadicLevelParameters

def quadraticFactor (D α : ℝ) : ℝ :=
  2 * quadraticConstant * D * (4 : ℝ) ^ α
def sexticFactor (D α : ℝ) : ℝ :=
  8 * sexticConstant * D ^ 3 * ((4 : ℝ) ^ α) ^ 3
def meanFactor (C α : ℝ) : ℝ := 64 * C * (4 : ℝ) ^ α

theorem parameter_bounds (D C : ℝ) (Q : ℕ) (T X α β : ℝ)
    (hD : 0 < D) (hC : 0 < C) (hQ : 1 ≤ Q)
    (hQX : (Q : ℝ) ≤ X ^ 2) (hX : 1 ≤ X)
    (hT : 1 ≤ T) (hTX : T ≤ X) (hα : 0 ≤ α) :
    quadratic Q 2 T (energy D Q α β X) ≤
      quadraticFactor D α * X ^ (2 * α + β) * (1 + Real.log X) ∧
    sextic Q 2 T (energy D Q α β X) ≤
      sexticFactor D α * (X ^ (2 * α + β)) ^ 3 *
        (1 + Real.log X) ^ 2 * T / (Q : ℝ) ^ 2 ∧
    meanSquare C Q T α β X ≤
      meanFactor C α * X ^ (2 * α + β) *
        (1 + Real.log X) * (1 + T / (Q : ℝ)) := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQp : (0 : ℝ) < Q := by linarith
  have hXp : 0 < X := by linarith
  have hlogs := log_bounds Q T X hQR hQX hX hT hTX
  have hpow : (4 * (Q : ℝ)) ^ α * X ^ β ≤
      (4 : ℝ) ^ α * X ^ (2 * α + β) := by
    calc
      _ = (4 : ℝ) ^ α * (Q : ℝ) ^ α * X ^ β := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hQp.le]
      _ ≤ (4 : ℝ) ^ α * (X ^ 2) ^ α * X ^ β := by
        gcongr
      _ = _ := by
        rw [← Real.rpow_natCast_mul hXp.le]
        norm_num only [Nat.cast_ofNat]
        rw [Real.rpow_add hXp]
        ring
  have hGT : 0 ≤ 1 + Real.log (T + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
    linarith
  have hGQ : 0 ≤ 1 + Real.log (4 * (Q : ℝ) + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ 4 * (Q : ℝ) + 1 by linarith)
    linarith
  have hGX : 0 ≤ 1 + Real.log X := by linarith [hlogs.1]
  have hqc : 0 ≤ quadraticConstant := by norm_num [quadraticConstant]
  have hbc : 0 ≤ sexticConstant := by norm_num [sexticConstant]
  refine ⟨?_, ?_, ?_⟩
  · rw [quadratic_eq D Q T α β X hQ]
    calc
      _ = quadraticConstant * D * ((4 * (Q : ℝ)) ^ α * X ^ β) *
          (1 + Real.log (T + 1)) := by ring
      _ ≤ quadraticConstant * D * ((4 : ℝ) ^ α * X ^ (2 * α + β)) *
          (2 * (1 + Real.log X)) := by
        gcongr
        exact hlogs.2.2.1
      _ = _ := by unfold quadraticFactor; ring
  · rw [sextic_eq D Q T α β X hQ]
    calc
      _ = sexticConstant * D ^ 3 * ((4 * (Q : ℝ)) ^ α * X ^ β) ^ 3 *
          (1 + Real.log (T + 1)) * (1 + Real.log (4 * (Q : ℝ) + 1)) *
            T / (Q : ℝ) ^ 2 := by ring
      _ ≤ sexticConstant * D ^ 3 * ((4 : ℝ) ^ α * X ^ (2 * α + β)) ^ 3 *
          (2 * (1 + Real.log X)) * (4 * (1 + Real.log X)) *
            T / (Q : ℝ) ^ 2 := by
        gcongr
        · exact hlogs.2.2.1
        · exact hlogs.2.2.2
      _ = _ := by unfold sexticFactor; ring
  · have hratio : 0 ≤ T / (Q : ℝ) := by positivity
    have hbracket : T / (Q : ℝ) + 16 * (1 + Real.log (4 * (Q : ℝ))) ≤
        64 * (1 + Real.log X) * (1 + T / (Q : ℝ)) := by
      nlinarith [hlogs.2.1, mul_nonneg hratio (Real.log_nonneg hX)]
    have hbracket0 : 0 ≤ T / (Q : ℝ) + 16 * (1 + Real.log (4 * (Q : ℝ))) := by
      have hh := Real.log_nonneg (show 1 ≤ 4 * (Q : ℝ) by linarith)
      positivity
    calc
      _ = C * ((4 * (Q : ℝ)) ^ α * X ^ β) *
          (T / (Q : ℝ) + 16 * (1 + Real.log (4 * (Q : ℝ)))) := by
        unfold meanSquare energy
        field_simp
      _ ≤ C * ((4 : ℝ) ^ α * X ^ (2 * α + β)) *
          (64 * (1 + Real.log X) * (1 + T / (Q : ℝ))) := by
        gcongr
      _ = _ := by unfold meanFactor; ring

theorem sextic_lower (D : ℝ) (Q : ℕ) (T X α β : ℝ)
    (hD : 0 < D) (hQ : 1 ≤ Q) (hQX : (Q : ℝ) ≤ X ^ 2)
    (hX : 1 ≤ X) (hT : 1 ≤ T) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    sexticConstant * D ^ 3 / X ^ 4 ≤
      sextic Q 2 T (energy D Q α β X) := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQp : (0 : ℝ) < Q := by linarith
  have hXp : 0 < X := by linarith
  have hp : 1 ≤ (4 * (Q : ℝ)) ^ α := Real.one_le_rpow (by linarith) hα
  have hβpow : 1 ≤ X ^ β := Real.one_le_rpow hX hβ
  have hGT : 1 ≤ 1 + Real.log (T + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
    linarith
  have hGQ : 1 ≤ 1 + Real.log (4 * (Q : ℝ) + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ 4 * (Q : ℝ) + 1 by linarith)
    linarith
  have hb : 0 ≤ sexticConstant := by norm_num [sexticConstant]
  have hQ2 : (Q : ℝ) ^ 2 ≤ X ^ 4 := by
    have hh := pow_le_pow_left₀ hQp.le hQX 2
    nlinarith
  rw [sextic_eq D Q T α β X hQ]
  calc
    _ ≤ sexticConstant * D ^ 3 / (Q : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hQ2
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        sexticConstant * D ^ 3 = sexticConstant * D ^ 3 * 1 ^ 3 * 1 ^ 3 * 1 * 1 * 1 := by ring
        _ ≤ _ := by gcongr

end ProductParameterEnvelope

#print axioms ProductParameterEnvelope.parameter_bounds
run_cmd do
  for target in [``ProductParameterEnvelope.parameter_bounds,
      ``ProductParameterEnvelope.sextic_lower] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "PRODUCT PARAMETER ENVELOPE PASSED"
