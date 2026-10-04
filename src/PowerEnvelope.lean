import PowerParameterEnvelope
import PolynomialLogEnvelope

/-!
For each fixed positive power h, a quantified coefficient-energy loss
can be absorbed into an arbitrary ambient power δ. The bounds are
uniform in N and T within the stated range.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter

namespace PowerEnvelope
open PowerMomentParameters PowerParameterEnvelope
open NormalizedPowerLevel DyadicLevelParameters

theorem eventually_bound (D C : ℝ) (h : ℕ) (δ : ℝ)
    (hD : 0 < D) (hC : 0 < C) (hh : 1 ≤ h) (hδ : 0 < δ) :
    let α := δ / (100 * ((h : ℝ) + 1))
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ (N : ℕ) (T : ℝ),
      1 ≤ N → (N : ℝ) ≤ X → 1 ≤ T → T ≤ X →
      quadratic (N ^ h) h T (energyBudget D N h α (X ^ α)) ≤
        X ^ δ ∧
      sextic (N ^ h) h T (energyBudget D N h α (X ^ α)) ≤
        X ^ δ * T / (N : ℝ) ^ (2 * h) ∧
      meanEven C N h T α α X ≤
        X ^ δ * (1 + T / (N : ℝ) ^ h) := by
  dsimp
  let α := δ / (100 * ((h : ℝ) + 1))
  let ν := α + h * α
  have hhR : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hh1 : (h : ℝ) + 1 ≠ 0 := by positivity
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hν : ν = δ / 100 := by
    dsimp [ν, α]
    field_simp
    ring
  have hgap : 0 < δ - ν := by rw [hν]; linarith
  have hgap3 : 0 < δ - 3 * ν := by rw [hν]; linarith
  have hQ : 0 ≤ quadraticFactor D α h := by
    unfold quadraticFactor quadraticConstant
    positivity
  have hB : 0 ≤ sexticFactor D α h := by
    unfold sexticFactor sexticConstant
    positivity
  have hM : 0 ≤ meanFactor C α h := by
    unfold meanFactor
    positivity
  filter_upwards [PolynomialLogEnvelope.eventually_bound
      (quadraticFactor D α h) 1 (δ - ν) hQ hgap,
    PolynomialLogEnvelope.eventually_bound
      (sexticFactor D α h) 2 (δ - 3 * ν) hB hgap3,
    PolynomialLogEnvelope.eventually_bound
      (meanFactor C α h) 1 (δ - ν) hM hgap]
    with X hq hb hm
  refine ⟨hq.1, ?_⟩
  intro N T hN hNX hT hTX
  have hXp : 0 < X := by linarith [hq.1]
  have hbounds := parameter_bounds D C N h T X α α
    hD hC hN hNX hT hTX hα
  have hquad : quadraticFactor D α h * X ^ ν *
      (1 + Real.log X) ≤ X ^ δ := by
    calc
      _ = (quadraticFactor D α h * (1 + Real.log X) ^ 1) *
          X ^ ν := by ring
      _ ≤ X ^ (δ - ν) * X ^ ν :=
        mul_le_mul_of_nonneg_right hq.2 (by positivity)
      _ = _ := by rw [← Real.rpow_add hXp]; congr 1; ring
  have hsextic : sexticFactor D α h * (X ^ ν) ^ 3 *
      (1 + Real.log X) ^ 2 ≤ X ^ δ := by
    calc
      _ = (sexticFactor D α h * (1 + Real.log X) ^ 2) *
          (X ^ ν) ^ 3 := by ring
      _ ≤ X ^ (δ - 3 * ν) * (X ^ ν) ^ 3 :=
        mul_le_mul_of_nonneg_right hb.2 (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul_natCast hXp.le, ← Real.rpow_add hXp]
        congr 1
        norm_num
        ring
  have hmean : meanFactor C α h * X ^ ν *
      (1 + Real.log X) ≤ X ^ δ := by
    calc
      _ = (meanFactor C α h * (1 + Real.log X) ^ 1) *
          X ^ ν := by ring
      _ ≤ X ^ (δ - ν) * X ^ ν :=
        mul_le_mul_of_nonneg_right hm.2 (by positivity)
      _ = _ := by rw [← Real.rpow_add hXp]; congr 1; ring
  refine ⟨hbounds.1.trans hquad, hbounds.2.1.trans ?_,
    hbounds.2.2.trans ?_⟩
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsextic (by linarith))
      (by positivity)
  · exact mul_le_mul_of_nonneg_right hmean (by positivity)

end PowerEnvelope

#print axioms PowerEnvelope.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``PowerEnvelope.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "POWER ENVELOPE PASSED"
