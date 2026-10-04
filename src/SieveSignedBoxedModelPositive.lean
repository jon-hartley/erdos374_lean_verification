import SieveSignedBoxedMainTermReduction
import PositiveInteriorModelClosed

/-! Unconditional positivity of the actual signed main-term MODEL.
The positive term is the explicit finite Mangoldt dyadic model, not an
actual short-window triple count. Their arithmetic discrepancy and all
signed divisor remainders remain outside this conclusion. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real
namespace SieveSignedBoxedModelPositive
open SieveWeightedScalarBudget SieveWeightedCutoffs
open SieveBoxedWeightedMainTerms
open SieveCappedUpperMainTerms (cappedFourth)
open SieveStoppingExpansion

theorem eventually_model_positive_with_reserve :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/1000 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ X₀ : ℝ, 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ S₂ S₃ : Finset ℕ,
      (∀ p ∈ S₂, p.Prime ∧ X^(9/35:ℝ) ≤ (p:ℝ) ∧ (p:ℝ) ≤ sqrt (2*X)) →
      (∀ p ∈ S₃, p.Prime ∧ X^alpha s ≤ (p:ℝ) ∧ (p:ℝ) ≤ X^(9/35:ℝ)) →
      (3/100:ℝ)*primeEuler (X^alpha s)+(1/1000)/log X <
        SieveBoxedWindow.mainTerm (level X s) s (X^alpha s)-
          boxedMass X s S₂ (cutoffThree X s)-boxedMass X s S₃ (cappedFourth X s)+
            PositiveInteriorModel.model X := by
  obtain ⟨s₀, hs₀, hs1, hb⟩ :=
    SieveSignedBoxedMainTermReduction.positive_of_positive_contribution
  obtain ⟨M, _hM, hm⟩ := PositiveInteriorModel.eventual_model_lower_reserve
  refine ⟨s₀, hs₀, hs1, ?_⟩
  intro s hs hss
  obtain ⟨A, hA, hB⟩ := hb s hs hss
  refine ⟨max A M, hA.trans_le (le_max_left _ _), ?_⟩
  intro X hX S₂ S₃ hS₂ hS₃
  have hbase := hB X ((le_max_left _ _).trans hX) S₂ S₃ ((7/50)/log X)
    hS₂ hS₃ le_rfl
  have hmodel := hm X ((le_max_right _ _).trans hX)
  have hsplit : (141/1000:ℝ)/log X=(7/50)/log X+(1/1000)/log X := by ring
  rw [hsplit] at hmodel
  linarith

run_cmd do
  for decl in [``eventually_model_positive_with_reserve] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL SIGNED BOXED MAIN-TERM MODEL POSITIVE WITH RESERVE; ARITHMETIC COUNT TRANSFER OPEN"
end SieveSignedBoxedModelPositive
end
