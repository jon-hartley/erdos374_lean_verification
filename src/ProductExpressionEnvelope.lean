import ProductMomentExpression
import MomentGrowthEnvelope
import MomentSavingEnvelope
import MomentCutoffEnvelope

/-!
Uniform growth and saving bounds for the complete mixed-product moment
expression. The cap's effect on the actual integral is handled by
ProductMomentExpression.integral_bound, including its power condition.
-/

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
open Filter

namespace ProductExpressionEnvelope
open ProductMomentParameters ProductParameterEnvelope DyadicLevelParameters
open ProductMomentExpression SupremumMoment MomentThreshold

def lowerConstant (D : ℝ) : ℝ := min 1 (sexticConstant * D ^ 3)

theorem lowerConstant_positive (D : ℝ) (hD : 0 < D) : 0 < lowerConstant D := by
  unfold lowerConstant sexticConstant
  positivity

theorem sextic_lower_bound (D : ℝ) (Q : ℕ) (T X α β : ℝ)
    (hD : 0 < D) (hQ : 1 ≤ Q) (hQX : (Q : ℝ) ≤ X ^ 2)
    (hX : 1 ≤ X) (hT : 1 ≤ T) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    lowerConstant D / X ^ (4 : ℝ) ≤ sextic Q 2 T (energy D Q α β X) := by
  have hh := ProductParameterEnvelope.sextic_lower D Q T X α β
    hD hQ hQX hX hT hα hβ
  norm_cast
  exact (div_le_div_of_nonneg_right (min_le_right 1 (sexticConstant * D ^ 3))
    (by positivity)).trans hh

theorem eventually_growth_bound (D C α β u δ : ℝ)
    (hD : 0 < D) (hC : 0 < C) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hu : 0 ≤ u) (hδ : 0 < δ) (hmargin : 3 * (2 * α + β) < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ (Q : ℕ) (T U p : ℝ),
      1 ≤ Q → (Q : ℝ) ≤ X ^ 2 → 1 ≤ T → T ≤ X →
      2 ≤ p → p ≤ 3 → T ^ (4 : ℕ) ≤ (Q : ℝ) ^ (p + 2) → U ≤ X ^ u →
      upperBound D C Q T α β X U p (X ^ δ) ≤ 26 * X ^ (3 * δ) := by
  have hc := lowerConstant_positive D hD
  have hc1 : lowerConstant D ≤ 1 := min_le_left _ _
  filter_upwards [ProductLossEnvelope.eventually_bound D C α β δ
    hD hC hα hβ hmargin,
    MomentCutoffEnvelope.eventually_band_bound (lowerConstant D) 4 δ u δ
      hc hc1 (by norm_num) hu hδ] with X he hb
  refine ⟨he.1, ?_⟩
  intro Q T U p hQ hQX hT hTX hp hp3 hlength hU
  have hXp : 0 < X := by linarith [he.1]
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQp : (0 : ℝ) < Q := by linarith
  have hTp : 0 < T := by linarith
  let E := energy D Q α β X
  let A := quadratic Q 2 T E
  let B := sextic Q 2 T E
  let V := meanSquare C Q T α β X
  let J := bandCountBound (cutoff B (X ^ δ) p) U
  have hE : 0 < E := by dsimp [E, energy]; positivity
  have hA : 0 ≤ A := quadratic_nonnegative _ _ _ _ hTp.le hE.le
  have hB : 0 < B := sextic_positive _ _ _ _ hQ (by norm_num) hTp hE
  have hlog : 0 ≤ Real.log (4 * (Q : ℝ)) := Real.log_nonneg (by linarith)
  have hV : 0 ≤ V := by dsimp [V, meanSquare, energy]; positivity
  have hpms := he.2 Q T hQ hQX hT hTX
  have hj : J ≤ X ^ δ := hb.2 B U p hp hp3
    (sextic_lower_bound D Q T X α β hD hQ hQX he.1 hT hα hβ) hU
  exact MomentGrowthEnvelope.bound X δ Q T p A B V J he.1 hδ hQR hTp
    hp hp3 hlength hA hB hV (bandCountBound_nonneg _ _)
    hpms.1 hpms.2.1 hpms.2.2 hj

theorem eventually_saving_bound (D C α β η s θ : ℝ)
    (hD : 0 < D) (hC : 0 < C) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hη : 0 < η) (hs : 0 < s) (hs1 : s ≤ 1)
    (hθ : 0 < θ) (hθη : θ ≤ η * s / 8)
    (hmargin : 3 * (2 * α + β) < θ / 10) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ (Q : ℕ) (T U p : ℝ),
      1 ≤ Q → (Q : ℝ) ≤ X ^ 2 → 1 ≤ T → T ≤ X →
      2 + s ≤ p → p ≤ 3 → X ^ η ≤ (Q : ℝ) →
      T ^ (4 : ℕ) * (X ^ η) ^ (p + 2) ≤ (Q : ℝ) ^ (p + 2) → U ≤ 1 →
      upperBound D C Q T α β X U p (X ^ (-θ)) ≤ 26 * X ^ (-θ / 2) := by
  have hc := lowerConstant_positive D hD
  have hc1 : lowerConstant D ≤ 1 := min_le_left _ _
  filter_upwards [ProductLossEnvelope.eventually_bound D C α β (θ / 10)
    hD hC hα hβ hmargin,
    MomentCutoffEnvelope.eventually_band_bound (lowerConstant D) 4 (-θ) 0 (θ / 10)
      hc hc1 (by norm_num) (by norm_num) (by positivity)] with X he hb
  refine ⟨he.1, ?_⟩
  intro Q T U p hQ hQX hT hTX hp hp3 hQlow hlength hU
  have hXp : 0 < X := by linarith [he.1]
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQp : (0 : ℝ) < Q := by linarith
  have hTp : 0 < T := by linarith
  let E := energy D Q α β X
  let A := quadratic Q 2 T E
  let B := sextic Q 2 T E
  let V := meanSquare C Q T α β X
  let J := bandCountBound (cutoff B (X ^ (-θ)) p) U
  have hE : 0 < E := by dsimp [E, energy]; positivity
  have hA : 0 ≤ A := quadratic_nonnegative _ _ _ _ hTp.le hE.le
  have hB : 0 < B := sextic_positive _ _ _ _ hQ (by norm_num) hTp hE
  have hlog : 0 ≤ Real.log (4 * (Q : ℝ)) := Real.log_nonneg (by linarith)
  have hV : 0 ≤ V := by dsimp [V, meanSquare, energy]; positivity
  have hpms := he.2 Q T hQ hQX hT hTX
  have hj : J ≤ X ^ (θ / 10) := hb.2 B U p (by linarith) hp3
    (sextic_lower_bound D Q T X α β hD hQ hQX he.1 hT hα hβ)
    (by simpa using hU)
  exact MomentSavingEnvelope.bound X η s θ Q T p A B V J he.1 hη hs hs1 hθ hθη
    hQlow hTp hp hp3 hlength hA hB hV (bandCountBound_nonneg _ _)
    hpms.1 hpms.2.1 hpms.2.2 hj

end ProductExpressionEnvelope

#print axioms ProductExpressionEnvelope.eventually_growth_bound
#print axioms ProductExpressionEnvelope.eventually_saving_bound
run_cmd do
  for target in [``ProductExpressionEnvelope.sextic_lower_bound,
      ``ProductExpressionEnvelope.eventually_growth_bound,
      ``ProductExpressionEnvelope.eventually_saving_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "PRODUCT EXPRESSION ENVELOPE PASSED"
