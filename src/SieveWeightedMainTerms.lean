import SieveWeightedFiniteSums
import SieveUpperCertified

/-! Instantiate the actual finite weighted prime sums with the certified
ordinary upper selector, uniformly in both s and X. Arithmetic remainders
and boxed upper constructions remain separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real Filter
open scoped BigOperators Topology
namespace SieveWeightedMainTerms
open SieveWeightedScalarBudget SieveWeightedCutoffs SieveStoppingExpansion

theorem eventually_negative_main_terms :
    ∃ s₀ X₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/1000 ∧ 1 < X₀ ∧
      ∀ s X : ℝ, 0 ≤ s → s < s₀ → X₀ ≤ X →
      ∀ S₂ S₃ : Finset ℕ,
      (∀ p ∈ S₂, p.Prime ∧ X^(9/35:ℝ) ≤ (p:ℝ) ∧ (p:ℝ) ≤ sqrt (2*X)) →
      (∀ p ∈ S₃, p.Prime ∧ X^alpha s ≤ (p:ℝ) ∧ (p:ℝ) ≤ X^(9/35:ℝ)) →
      mass X s S₂ (cutoffThree X s)+mass X s S₃ (cutoffFour X s) ≤
        (1-1847/2677500:ℝ)*primeEuler (X^alpha s) := by
  obtain ⟨Z, _hZ, hu⟩ := SieveUpperCertified.eventual_full_upper
  obtain ⟨δ, A, hδ, hA, hb⟩ := SieveWeightedScalarBudget.uniformly_large_X
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/7)).eventually_ge_atTop Z)
  refine ⟨min δ (1/1000), max A (max B (exp 1000)), lt_min hδ (by norm_num),
    min_le_right _ _, hA.trans_le (le_max_left _ _), ?_⟩
  intro s X hs hss hX S₂ S₃ hS₂ hS₃
  have hXA : A ≤ X := (le_max_left _ _).trans hX
  have hX1 : 1 < X := hA.trans_le hXA
  have hs1 : s ≤ 1/1000 := hss.le.trans (min_le_right _ _)
  have hlog : 1000 ≤ log X := by
    simpa only [log_exp] using log_le_log (exp_pos (1000:ℝ))
      ((le_max_right _ _).trans ((le_max_right _ _).trans hX))
  have hXZ : Z ≤ X^(1/7:ℝ) := hB X
    ((le_max_left _ _).trans ((le_max_right _ _).trans hX))
  have ha := hb s X (by simpa only [abs_of_nonneg hs] using hss.trans_le (min_le_left _ _)) hXA
  exact (combined_bound X s Z S₂ S₃ hX1 hs hs1 hlog hXZ hu hS₂ hS₃).trans
    (mul_le_mul_of_nonneg_right ha (SieveEulerRatio.euler_pos _).le)

run_cmd do
  for decl in [``eventually_negative_main_terms] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL TWO NEGATIVE ORDINARY MAIN TERMS BELOW V; DIVISOR REMAINDERS OPEN"
end SieveWeightedMainTerms
end
