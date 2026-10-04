import TripleAdoptEighthParameterEnvelope
import PolynomialLogEnvelope

/-!
For the fixed loss alpha=kappa/100, all coefficient logarithms fit
inside X^(kappa/10), uniformly in the polynomial length and duration.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter

namespace TripleAdoptEighthPowerEnvelope
open EighthMomentParameters TripleAdoptEighthParameterEnvelope NormalizedPowerLevel
open DyadicLevelParameters FlatEighthMoment

theorem eventually_bound (D C κ : ℝ) (hD : 0 < D) (hC : 0 < C) (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ (N : ℕ) (T : ℝ),
      1 ≤ N → (N : ℝ) ≤ X → 1 ≤ T → T ≤ X →
      quadratic (N ^ 3) 3 T (energyBudget D N 3 (κ / 100) 1) ≤ X ^ (κ / 10) ∧
      sextic (N ^ 3) 3 T (energyBudget D N 3 (κ / 100) 1) ≤
        X ^ (κ / 10) * T / (N : ℝ) ^ 6 ∧
      meanSix C N T (κ / 100) ≤ X ^ (κ / 10) * (1 + T / (N : ℝ) ^ 3) := by
  let α := κ / 100
  let δ := κ / 10
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hgap : 0 < δ - α := by dsimp [δ, α]; linarith
  have hgap3 : 0 < δ - 3 * α := by dsimp [δ, α]; linarith
  have hQ : 0 ≤ quadraticFactor D α := by
    unfold quadraticFactor quadraticConstant
    positivity
  have hB : 0 ≤ sexticFactor D α := by
    unfold sexticFactor sexticConstant
    positivity
  have hM : 0 ≤ meanFactor C α := by unfold meanFactor; positivity
  filter_upwards [PolynomialLogEnvelope.eventually_bound (quadraticFactor D α) 1 (δ - α) hQ hgap,
    PolynomialLogEnvelope.eventually_bound (sexticFactor D α) 2 (δ - 3 * α) hB hgap3,
    PolynomialLogEnvelope.eventually_bound (meanFactor C α) 1 (δ - α) hM hgap]
    with X hq hb hm
  refine ⟨hq.1, ?_⟩
  intro N T hN hNX hT hTX
  have hXp : 0 < X := by linarith [hq.1]
  have hbounds := parameter_bounds D C N T X α hD hC hN hNX hT hTX hα
  have hquad : quadraticFactor D α * X ^ α * (1 + Real.log X) ≤ X ^ δ := by
    calc
      _ = (quadraticFactor D α * (1 + Real.log X) ^ 1) * X ^ α := by ring
      _ ≤ X ^ (δ - α) * X ^ α := mul_le_mul_of_nonneg_right hq.2 (by positivity)
      _ = _ := by rw [← Real.rpow_add hXp]; congr 1; ring
  have hsextic : sexticFactor D α * (X ^ α) ^ 3 * (1 + Real.log X) ^ 2 ≤ X ^ δ := by
    calc
      _ = (sexticFactor D α * (1 + Real.log X) ^ 2) * (X ^ α) ^ 3 := by ring
      _ ≤ X ^ (δ - 3 * α) * (X ^ α) ^ 3 := mul_le_mul_of_nonneg_right hb.2 (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul_natCast hXp.le, ← Real.rpow_add hXp]
        congr 1
        norm_num
        ring
  have hmean : meanFactor C α * X ^ α * (1 + Real.log X) ≤ X ^ δ := by
    calc
      _ = (meanFactor C α * (1 + Real.log X) ^ 1) * X ^ α := by ring
      _ ≤ X ^ (δ - α) * X ^ α := mul_le_mul_of_nonneg_right hm.2 (by positivity)
      _ = _ := by rw [← Real.rpow_add hXp]; congr 1; ring
  refine ⟨hbounds.1.trans hquad, hbounds.2.1.trans ?_, hbounds.2.2.trans ?_⟩
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsextic (by linarith)) (by positivity)
  · exact mul_le_mul_of_nonneg_right hmean (by positivity)

end TripleAdoptEighthPowerEnvelope

#print axioms TripleAdoptEighthPowerEnvelope.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``TripleAdoptEighthPowerEnvelope.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "EIGHTH POWER ENVELOPE PASSED"
