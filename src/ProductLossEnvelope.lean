import ProductParameterEnvelope
import PolynomialLogEnvelope

/-!
Arbitrary nonnegative coefficient losses for the mixed-product envelope.
The sextic condition 3 * (2 * alpha + beta) < delta leaves room to absorb
the coefficient logarithms into X^delta. This follows ProductPowerEnvelope
without changing its fixed-loss theorem or interface.

The energy identity allows both coefficient families to carry powers of
the ambient scale; their exponents add in ProductMomentParameters.energy.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter

namespace ProductLossEnvelope
open ProductMomentParameters ProductParameterEnvelope
open DyadicLevelParameters

theorem energy_eq (D : ℝ) (K M : ℕ) (α β₁ β₂ X : ℝ) (hX : 0 < X) :
    NormalizedProductLevel.energyBudget D K M α (X ^ β₁) (X ^ β₂) =
      ProductMomentParameters.energy D (K * M) α (β₁ + β₂) X := by
  unfold NormalizedProductLevel.energyBudget ProductMomentParameters.energy
  rw [Real.rpow_add hX]
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev,
    mul_assoc]
  ring

theorem eventually_bound (D C α β δ : ℝ)
    (hD : 0 < D) (hC : 0 < C) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hmargin : 3 * (2 * α + β) < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ (N : ℕ) (T : ℝ),
      1 ≤ N → (N : ℝ) ≤ X ^ 2 → 1 ≤ T → T ≤ X →
      quadratic N 2 T (energy D N α β X) ≤ X ^ δ ∧
      sextic N 2 T (energy D N α β X) ≤
        X ^ δ * T / (N : ℝ) ^ 2 ∧
      meanSquare C N T α β X ≤ X ^ δ * (1 + T / (N : ℝ)) := by
  let ν := 2 * α + β
  have hν : 0 ≤ ν := by dsimp [ν]; positivity
  have hgap : 0 < δ - ν := by dsimp [ν] at *; linarith
  have hgap3 : 0 < δ - 3 * ν := by dsimp [ν]; linarith
  have hQ : 0 ≤ quadraticFactor D α := by
    unfold quadraticFactor quadraticConstant
    positivity
  have hB : 0 ≤ sexticFactor D α := by
    unfold sexticFactor sexticConstant
    positivity
  have hM : 0 ≤ meanFactor C α := by unfold meanFactor; positivity
  filter_upwards [
    PolynomialLogEnvelope.eventually_bound (quadraticFactor D α) 1
      (δ - ν) hQ hgap,
    PolynomialLogEnvelope.eventually_bound (sexticFactor D α) 2
      (δ - 3 * ν) hB hgap3,
    PolynomialLogEnvelope.eventually_bound (meanFactor C α) 1
      (δ - ν) hM hgap] with X hq hb hm
  refine ⟨hq.1, ?_⟩
  intro N T hN hNX hT hTX
  have hXp : 0 < X := by linarith [hq.1]
  have hbounds := parameter_bounds D C N T X α β
    hD hC hN hNX hq.1 hT hTX hα
  have hquad : quadraticFactor D α * X ^ ν * (1 + Real.log X) ≤
      X ^ δ := by
    calc
      _ = (quadraticFactor D α * (1 + Real.log X) ^ 1) * X ^ ν := by
        ring
      _ ≤ X ^ (δ - ν) * X ^ ν :=
        mul_le_mul_of_nonneg_right hq.2 (by positivity)
      _ = _ := by rw [← Real.rpow_add hXp]; congr 1; ring
  have hsextic : sexticFactor D α * (X ^ ν) ^ 3 *
      (1 + Real.log X) ^ 2 ≤ X ^ δ := by
    calc
      _ = (sexticFactor D α * (1 + Real.log X) ^ 2) * (X ^ ν) ^ 3 := by
        ring
      _ ≤ X ^ (δ - 3 * ν) * (X ^ ν) ^ 3 :=
        mul_le_mul_of_nonneg_right hb.2 (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul_natCast hXp.le, ← Real.rpow_add hXp]
        congr 1
        norm_num
        ring
  have hmean : meanFactor C α * X ^ ν * (1 + Real.log X) ≤ X ^ δ := by
    calc
      _ = (meanFactor C α * (1 + Real.log X) ^ 1) * X ^ ν := by ring
      _ ≤ X ^ (δ - ν) * X ^ ν :=
        mul_le_mul_of_nonneg_right hm.2 (by positivity)
      _ = _ := by rw [← Real.rpow_add hXp]; congr 1; ring
  refine ⟨hbounds.1.trans hquad, hbounds.2.1.trans ?_, hbounds.2.2.trans ?_⟩
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsextic (by linarith)) (by positivity)
  · exact mul_le_mul_of_nonneg_right hmean (by positivity)

end ProductLossEnvelope

#print axioms ProductLossEnvelope.energy_eq
#print axioms ProductLossEnvelope.eventually_bound
run_cmd do
  for target in [``ProductLossEnvelope.energy_eq,
      ``ProductLossEnvelope.eventually_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "PRODUCT LOSS ENVELOPE PASSED"
