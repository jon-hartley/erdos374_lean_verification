import SieveFineFirstTerm
import SieveBoxedWeightedMainTerms
import SievePositiveScale
import SieveSignedMainTermReduction

/-! Actual lower and upper boxed main terms have a positive signed margin
under an explicit positive-contribution hypothesis. No divisor remainder,
dyadic source weight conversion or positive prime count is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real Filter
open scoped Topology
namespace SieveSignedBoxedMainTermReduction
open SieveWeightedScalarBudget SieveWeightedCutoffs
open SieveBoxedWeightedMainTerms
open SieveCappedUpperMainTerms (cappedFourth)
open SieveStoppingExpansion

theorem positive_of_positive_contribution :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/1000 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ X₀ : ℝ, 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ S₂ S₃ : Finset ℕ, ∀ P : ℝ,
      (∀ p ∈ S₂, p.Prime ∧ X^(9/35:ℝ) ≤ (p:ℝ) ∧ (p:ℝ) ≤ sqrt (2*X)) →
      (∀ p ∈ S₃, p.Prime ∧ X^alpha s ≤ (p:ℝ) ∧ (p:ℝ) ≤ X^(9/35:ℝ)) →
      (7/50)/log X ≤ P →
      (3/100:ℝ)*primeEuler (X^alpha s) ≤
        SieveBoxedWindow.mainTerm (level X s) s (X^alpha s)-
          boxedMass X s S₂ (cutoffThree X s)-boxedMass X s S₃ (cappedFourth X s)+P := by
  obtain ⟨sF, hsF, _hsHalf, hfirst⟩ :=
    SieveFineFirstTerm.mainTerm_at_first_cutoff (1/1000) (by norm_num)
  obtain ⟨sU, hsU, hsU1, hupper⟩ :=
    SieveBoxedWeightedMainTerms.eventually_negative_main_terms
  refine ⟨min sF sU, lt_min hsF hsU, (min_le_right _ _).trans hsU1, ?_⟩
  intro s hs hss
  have hssF : s < sF := hss.trans_le (min_le_left _ _)
  have hssU : s < sU := hss.trans_le (min_le_right _ _)
  have hs1 : s ≤ 1/1000 := hssU.le.trans hsU1
  obtain ⟨A, hA, hnegative⟩ := hupper s hs hssU
  obtain ⟨D₀, _hD₀, hfirstD⟩ := hfirst s hs hssF
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by linarith : (0:ℝ) < 1-3*s)).eventually_ge_atTop D₀)
  obtain ⟨C, _hC, hpositive⟩ :=
    SievePositiveScale.eventually_coefficient_comparison s (by linarith)
  refine ⟨max A (max B C), hA.trans_le (le_max_left _ _), ?_⟩
  intro X hX S₂ S₃ P hS₂ hS₃ hP
  have hXA : A ≤ X := (le_max_left _ _).trans hX
  have hX1 : 1 < X := hA.trans_le hXA
  have hD : D₀ ≤ level X s := hB X
    ((le_max_left _ _).trans ((le_max_right _ _).trans hX))
  have hf := hfirstD (level X s) hD
  rw [SieveSignedMainTermReduction.first_cutoff_eq X s (by linarith)] at hf
  have hu := hnegative X hXA S₂ S₃ hS₂ hS₃
  have hp := (hpositive X
    ((le_max_right _ _).trans ((le_max_right _ _).trans hX))).trans hP
  change ((104/1875)*(1-3*s))*primeEuler (X^alpha s) ≤ P at hp
  have hV : 0 ≤ primeEuler (X^alpha s) := (SieveEulerRatio.euler_pos _).le
  have hsV : s*primeEuler (X^alpha s) ≤ (1/1000)*primeEuler (X^alpha s) :=
    mul_le_mul_of_nonneg_right hs1 hV
  nlinarith

run_cmd do
  for decl in [``positive_of_positive_contribution] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL BOXED MAIN-TERM REDUCTION; POSITIVE ARITHMETIC CONTRIBUTION EXPLICITLY ASSUMED"
end SieveSignedBoxedMainTermReduction
end
