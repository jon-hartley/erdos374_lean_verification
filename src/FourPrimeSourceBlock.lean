import FourPrimeBlock
import FourPrimeSourceData

/-! The actual four-prime source remainder is an application of the generic
block bound to the checked elementary source-data conversion. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace FourPrimeSourceBlock
open FourPrimeScaleBudget
theorem eventually_bound (s : ℝ) (hs : 0 < s) (hs1 : s < 1 / 100) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ B : Data s X,
        let Y := FactoredDivisorVariableWindow.sourceWindow s X
        (1 / X) * (∫ x in Icc X (2 * X),
          remainder B (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  obtain ⟨c, hc, hgeneric⟩ := FourPrimeBlock.eventually_bound s hs hs1
  refine ⟨c, hc, ?_⟩
  filter_upwards [hgeneric] with X hh
  refine ⟨hh.1, ?_⟩
  intro B
  have hresult := hh.2 (FourPrimeGrouping.support B.S0 B.S1 B.S2 B.S3) B.S4
    (FourPrimeGrouping.coefficient B.S0 B.S1 B.S2 B.S3 B.C)
    (FourPrimeGrouping.lastCoefficient B.S4)
    (left_support_two_le B) (last_support_two_le B)
    (last_support_lower B hh.1) (last_support_upper B hh.1 hs hs1)
    (cross_product_bound B hh.1 hs hs1)
    (left_coefficient_bound B) (last_coefficient_bound B)
  change (1 / X) * (∫ x in Icc X (2 * X),
    HarmanDivisorWindow.remainder
      (FourPrimeGrouping.fullSupport B.S0 B.S1 B.S2 B.S3 B.S4)
      (FourPrimeGrouping.fullCoefficient B.S0 B.S1 B.S2 B.S3 B.S4 B.C)
      (x - x * (FactoredDivisorVariableWindow.sourceWindow s X / X)) x ^ 2) ≤ _ at hresult
  simpa only [grouped_remainder_eq] using hresult
theorem eventually_point101 :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ B : Data (1 / 1000) X,
        let Y : ℝ := (1 / 2) * X ^ (101 / 1000 : ℝ)
        (1 / X) * (∫ x in Icc X (2 * X),
          remainder B (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  simpa only [FactoredDivisorVariableWindow.sourceWindow,
    show (1 / 10 : ℝ) + 1 / 1000 = 101 / 1000 by norm_num] using
      eventually_bound (1 / 1000) (by norm_num) (by norm_num)

end FourPrimeSourceBlock

#print axioms FourPrimeSourceBlock.eventually_bound
run_cmd do
  for target in [``FourPrimeSourceBlock.eventually_bound,
      ``FourPrimeSourceBlock.eventually_point101] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOUR PRIME SOURCE BLOCK PASSED; SIEVE COEFFICIENT CONSTRUCTION REMAINS OPEN"

end
