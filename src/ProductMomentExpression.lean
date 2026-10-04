import NormalizedProductMoment
import ProductLossEnvelope

/-!
Write the proved mixed-product moment bound with two coefficient-energy
exponents. This is the common expression used by the growth and saving
applications; its full-product cap remains an explicit input.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ProductMomentExpression
open Erdos374.HarmanGram152 ProductMomentParameters DyadicLevelParameters
open SupremumMoment MomentThreshold

def upperBound (D C : ℝ) (Q : ℕ) (T α β X U p μ : ℝ) : ℝ :=
  let E := energy D Q α β X
  let A := quadratic Q 2 T E
  let B := sextic Q 2 T E
  (B / μ) ^ ((p - 2) / (6 - p)) * meanSquare C Q T α β X +
    bandCountBound (cutoff B μ p) U * (2 : ℝ) ^ p *
      (A * (2 : ℝ) ^ (p - 2) + 1) * μ

theorem integral_bound (α : ℝ) (hα : 0 < α) :
    ∃ D : ℝ, 0 < D ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (K M : ℕ) (s r : Finset ℕ) (left right : ℕ → ℂ)
        (a T β₁ β₂ X σ U p μ : ℝ),
      1 ≤ K → 1 ≤ M → 0 < T → 0 < X → 1 ≤ σ →
      0 ≤ U → 2 ≤ p → p < 6 → 0 < μ →
      (∀ n ∈ s, K < n ∧ n ≤ 2 * K) →
      (∀ n ∈ r, M < n ∧ n ≤ 2 * M) →
      (∑ n ∈ s, ‖left n‖ ^ 2) ≤ X ^ β₁ * K →
      (∑ n ∈ r, ‖right n‖ ^ 2) ≤ X ^ β₂ * M →
      (∀ t ∈ Icc a (a + T),
        ‖verticalDirichlet152 s left σ t *
          verticalDirichlet152 r right σ t‖ ≤ U) →
      U ^ (p - 2) ≤ μ →
      (∫ t in Icc a (a + T),
        ‖verticalDirichlet152 s left σ t *
          verticalDirichlet152 r right σ t‖ ^ p) ≤
        upperBound D C (K * M) T α (β₁ + β₂) X U p μ := by
  obtain ⟨D, hD, C, hC, hm⟩ := NormalizedProductMoment.integral_bound α hα
  refine ⟨D, hD, C, hC, ?_⟩
  intro K M s r left right a T β₁ β₂ X σ U p μ
    hK hM hT hX hσ hU hp hp6 hμ hs hr he₁ he₂ hcap hpower
  have hh := hm K M s r left right a T (X ^ β₁) (X ^ β₂) σ U p μ
    hK hM hT (by positivity) (by positivity) hσ hU hp hp6 hμ
    hs hr he₁ he₂ hcap hpower
  dsimp only at hh
  rw [ProductLossEnvelope.energy_eq D K M α β₁ β₂ X hX,
    ProductLossEnvelope.energy_eq C K M α β₁ β₂ X hX] at hh
  convert hh using 1
  unfold upperBound meanSquare
  push_cast
  ring

end ProductMomentExpression

#print axioms ProductMomentExpression.integral_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``ProductMomentExpression.integral_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "PRODUCT MOMENT EXPRESSION PASSED"
