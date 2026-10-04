import SieveCappedUpperFinite
import SieveWeightedMainTerms

/-! The ordinary negative main-term budget with the fourth cutoff genuinely
at most its outer prime. The changed strip is bounded explicitly; source
count identities, boxed upper families and arithmetic remainders stay open. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real Filter
open scoped Topology
namespace SieveCappedUpperMainTerms
open SieveWeightedScalarBudget SieveWeightedCutoffs SieveWeightedMainTerms
open SieveStoppingExpansion

theorem eventually_negative_main_terms :
    ∃ s₀ X₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/1000 ∧ 1 < X₀ ∧
      ∀ s X : ℝ, 0 ≤ s → s < s₀ → X₀ ≤ X →
      ∀ S₂ S₃ : Finset ℕ,
      (∀ p ∈ S₂, p.Prime ∧ X^(9/35:ℝ) ≤ (p:ℝ) ∧ (p:ℝ) ≤ sqrt (2*X)) →
      (∀ p ∈ S₃, p.Prime ∧ X^alpha s ≤ (p:ℝ) ∧ (p:ℝ) ≤ X^(9/35:ℝ)) →
      mass X s S₂ (cutoffThree X s)+mass X s S₃ (cappedFourth X s) ≤
        (1-1847/5355000:ℝ)*primeEuler (X^alpha s) := by
  obtain ⟨sU, A, hsU, hsU1, hA, hu⟩ :=
    SieveWeightedMainTerms.eventually_negative_main_terms
  obtain ⟨δ, C, hδ, _hC, hc⟩ := eventually_strip_small
  obtain ⟨Z, _hZ, hupper⟩ := SieveUpperCertified.eventual_full_upper
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/7)).eventually_ge_atTop Z)
  refine ⟨min sU δ, max A (max C B), lt_min hsU hδ,
    (min_le_left _ _).trans hsU1, hA.trans_le (le_max_left _ _), ?_⟩
  intro s X hs hss hX S₂ S₃ hS₂ hS₃
  have hsU' : s < sU := hss.trans_le (min_le_left _ _)
  have hsδ : |s| < δ := by
    simpa only [abs_of_nonneg hs] using hss.trans_le (min_le_right _ _)
  have hs1 : s ≤ 1/1000 := hsU'.le.trans hsU1
  have hXA : A ≤ X := (le_max_left _ _).trans hX
  have hXC : C ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hXB : B ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hX1 : 1 < X := hA.trans_le hXA
  have hraw := hu s X hs hsU' hXA S₂ S₃ hS₂ hS₃
  have hcap := capped_sum_le X s Z S₃ hX1 hs hs1 (hB X hXB) hupper hS₃
  change mass X s S₃ (cappedFourth X s) ≤ mass X s S₃ (cutoffFour X s)+
    stripBudget s (1/log X)*primeEuler (X^alpha s) at hcap
  have hstrip := mul_le_mul_of_nonneg_right (hc s X hsδ hXC)
    (SieveEulerRatio.euler_pos (X^alpha s)).le
  linarith

run_cmd do
  for decl in [``eventually_negative_main_terms] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL CAPPED NEGATIVE MAIN TERMS BELOW V; COUNT AND REMAINDERS REMAIN OPEN"
end SieveCappedUpperMainTerms
end
