import PowerMomentParameters

/-!
Ambient envelopes for the whole hth power. The fixed energy loss X^β
appears h times, and the sixth moment has denominator N^(2h).
-/

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section

namespace PowerParameterEnvelope
open PowerMomentParameters NormalizedPowerLevel DyadicLevelParameters

def quadraticFactor (D α : ℝ) (h : ℕ) : ℝ :=
  2 * quadraticConstant h * D * (2 : ℝ) ^ α
def sexticFactor (D α : ℝ) (h : ℕ) : ℝ :=
  2 * ((h : ℝ) + 2) * sexticConstant h * D ^ 3 *
    ((2 : ℝ) ^ α) ^ 3
def meanFactor (C α : ℝ) (h : ℕ) : ℝ :=
  (1 + 4 * (2 : ℝ) ^ h * (1 + h)) * C * (2 : ℝ) ^ α

theorem parameter_bounds (D C : ℝ) (N h : ℕ)
    (T X α β : ℝ) (hD : 0 < D) (hC : 0 < C)
    (hN : 1 ≤ N) (hNX : (N : ℝ) ≤ X)
    (hT : 1 ≤ T) (hTX : T ≤ X) (hα : 0 ≤ α) :
    quadratic (N ^ h) h T (energyBudget D N h α (X ^ β)) ≤
      quadraticFactor D α h * X ^ (α + h * β) *
        (1 + Real.log X) ∧
    sextic (N ^ h) h T (energyBudget D N h α (X ^ β)) ≤
      sexticFactor D α h * (X ^ (α + h * β)) ^ 3 *
        (1 + Real.log X) ^ 2 * T / (N : ℝ) ^ (2 * h) ∧
    meanEven C N h T α β X ≤
      meanFactor C α h * X ^ (α + h * β) *
        (1 + Real.log X) * (1 + T / (N : ℝ) ^ h) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hX : 1 ≤ X := hNR.trans hNX
  have hXp : 0 < X := by linarith
  have hlogs := log_bounds N h T X hN hNX hT hTX
  have hpow : (2 * (N : ℝ)) ^ α * (X ^ β) ^ h ≤
      (2 : ℝ) ^ α * X ^ (α + h * β) := by
    calc
      _ = (2 : ℝ) ^ α * (N : ℝ) ^ α * (X ^ β) ^ h := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hNp.le]
      _ ≤ (2 : ℝ) ^ α * X ^ α * (X ^ β) ^ h := by
        gcongr
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_mul_natCast hXp.le,
          ← Real.rpow_add hXp]
        congr 1
        ring
  have hGT : 0 ≤ 1 + Real.log (T + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
    linarith
  have hGN : 0 ≤ 1 + Real.log
      ((2 : ℝ) ^ h * (N : ℝ) ^ h + 1) := by
    have hh := Real.log_nonneg
      (show 1 ≤ (2 : ℝ) ^ h * (N : ℝ) ^ h + 1 by
        nlinarith [mul_nonneg
          (show 0 ≤ (2 : ℝ) ^ h by positivity)
          (show 0 ≤ (N : ℝ) ^ h by positivity)])
    linarith
  have hGX : 0 ≤ 1 + Real.log X := by linarith [hlogs.1]
  have hq : 0 ≤ quadraticConstant h := by
    unfold quadraticConstant
    positivity
  have hb : 0 ≤ sexticConstant h := by
    unfold sexticConstant
    positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [quadratic_eq D N h T α β X hN]
    calc
      _ = quadraticConstant h * D *
          ((2 * (N : ℝ)) ^ α * (X ^ β) ^ h) *
            (1 + Real.log (T + 1)) := by ring
      _ ≤ quadraticConstant h * D *
          ((2 : ℝ) ^ α * X ^ (α + h * β)) *
            (2 * (1 + Real.log X)) := by
        gcongr
        exact hlogs.2.2.1
      _ = _ := by unfold quadraticFactor; ring
  · rw [sextic_eq D N h T α β X hN]
    calc
      _ = sexticConstant h * D ^ 3 *
          ((2 * (N : ℝ)) ^ α * (X ^ β) ^ h) ^ 3 *
          (1 + Real.log (T + 1)) *
          (1 + Real.log ((2 : ℝ) ^ h * (N : ℝ) ^ h + 1)) *
            T / (N : ℝ) ^ (2 * h) := by ring
      _ ≤ sexticConstant h * D ^ 3 *
          ((2 : ℝ) ^ α * X ^ (α + h * β)) ^ 3 *
          (2 * (1 + Real.log X)) *
          (((h : ℝ) + 2) * (1 + Real.log X)) *
            T / (N : ℝ) ^ (2 * h) := by
        gcongr
        · exact hlogs.2.2.1
        · exact hlogs.2.2.2
      _ = _ := by unfold sexticFactor; ring
  · have hR : 0 ≤ T / (N : ℝ) ^ h := by positivity
    have hL : 1 ≤ 1 + Real.log X := hlogs.1
    have hB : 0 ≤ 4 * (2 : ℝ) ^ h * (1 + h) := by
      positivity
    have hlogterm : 1 + (h : ℝ) * Real.log (2 * (N : ℝ)) ≤
        (1 + h) * (1 + Real.log X) := by
      nlinarith [hlogs.2.1, Real.log_nonneg hX]
    have hbracket : T / (N : ℝ) ^ h +
        4 * (2 : ℝ) ^ h *
          (1 + h * Real.log (2 * (N : ℝ))) ≤
        (1 + 4 * (2 : ℝ) ^ h * (1 + h)) *
          (1 + Real.log X) * (1 + T / (N : ℝ) ^ h) := by
      have hfirst := mul_le_mul_of_nonneg_left hlogterm
        (by positivity : 0 ≤ 4 * (2 : ℝ) ^ h)
      nlinarith [mul_nonneg (show 0 ≤ Real.log X by
        exact Real.log_nonneg hX) hR,
        mul_nonneg hB hR,
        mul_nonneg (mul_nonneg hB hR)
          (show 0 ≤ Real.log X by exact Real.log_nonneg hX)]
    have hbracket0 : 0 ≤ T / (N : ℝ) ^ h +
        4 * (2 : ℝ) ^ h *
          (1 + h * Real.log (2 * (N : ℝ))) := by
      have hh := Real.log_nonneg
        (show (1 : ℝ) ≤ 2 * (N : ℝ) by linarith)
      positivity
    calc
      _ = C * ((2 * (N : ℝ)) ^ α * (X ^ β) ^ h) *
          (T / (N : ℝ) ^ h +
            4 * (2 : ℝ) ^ h *
              (1 + h * Real.log (2 * (N : ℝ)))) := by
        unfold meanEven
        ring
      _ ≤ C * ((2 : ℝ) ^ α * X ^ (α + h * β)) *
          ((1 + 4 * (2 : ℝ) ^ h * (1 + h)) *
            (1 + Real.log X) * (1 + T / (N : ℝ) ^ h)) := by
        gcongr
      _ = _ := by unfold meanFactor; ring

theorem sextic_lower (D : ℝ) (N h : ℕ)
    (T X α β : ℝ) (hD : 0 < D) (hN : 1 ≤ N)
    (hNX : (N : ℝ) ≤ X) (hT : 1 ≤ T)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    sexticConstant h * D ^ 3 / X ^ (2 * h) ≤
      sextic (N ^ h) h T (energyBudget D N h α (X ^ β)) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hX : 1 ≤ X := hNR.trans hNX
  have hXp : 0 < X := by linarith
  have hp : 1 ≤ (2 * (N : ℝ)) ^ α :=
    Real.one_le_rpow (by linarith) hα
  have hβpow : 1 ≤ (X ^ β) ^ h :=
    one_le_pow₀ (Real.one_le_rpow hX hβ)
  have hGT : 1 ≤ 1 + Real.log (T + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
    linarith
  have hGN : 1 ≤ 1 + Real.log
      ((2 : ℝ) ^ h * (N : ℝ) ^ h + 1) := by
    have hh := Real.log_nonneg
      (show 1 ≤ (2 : ℝ) ^ h * (N : ℝ) ^ h + 1 by
        nlinarith [mul_nonneg
          (show 0 ≤ (2 : ℝ) ^ h by positivity)
          (show 0 ≤ (N : ℝ) ^ h by positivity)])
    linarith
  have hb : 0 ≤ sexticConstant h := by
    unfold sexticConstant
    positivity
  rw [sextic_eq D N h T α β X hN]
  calc
    _ ≤ sexticConstant h * D ^ 3 / (N : ℝ) ^ (2 * h) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hNp.le hNX (2 * h))
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        sexticConstant h * D ^ 3 =
            sexticConstant h * D ^ 3 * 1 ^ 3 * 1 ^ 3 * 1 * 1 * 1 := by ring
        _ ≤ _ := by gcongr

end PowerParameterEnvelope

#print axioms PowerParameterEnvelope.parameter_bounds
run_cmd do
  for target in [``PowerParameterEnvelope.parameter_bounds,
      ``PowerParameterEnvelope.sextic_lower] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "POWER PARAMETER ENVELOPE PASSED"
