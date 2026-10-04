import PositiveSharpRemainderAnalysis
import SieveUpperBoxWindow

/-! The full, literal lower and upper boxed coefficient families satisfy a
fixed-length divisor-multiplicity bound. The cap is uniform in D and z.
No assertion is made that their support has a particular ambient scale,
or that the accepted families factor into analytic two-factor blocks. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PositiveSharpRemainderAnalysisBoxed
open PositiveSharpRemainderAnalysis

theorem lower_lengths (D s z : ℝ) :
    (∀ t ∈ SieveCompleteBoxing.innerFamily D s z, t.length ≤ SieveBoxLength.cutoff s) ∧
    (∀ t ∈ SieveCompleteBoxing.outerFamily D s z, t.length ≤ SieveBoxLength.cutoff s) := by
  constructor <;> intro t ht
  · exact ((SieveBoxedFamily.mem_boundedTuples _ _ _).mp (Finset.mem_filter.mp ht).1).1
  · exact ((SieveBoxedFamily.mem_boundedTuples _ _ _).mp (Finset.mem_filter.mp ht).1).1

theorem upper_lengths (D s z : ℝ) :
    (∀ t ∈ SieveUpperBoxing.outerFamily D s z, t.length ≤ SieveBoxLength.cutoff s) ∧
    (∀ t ∈ SieveUpperBoxing.innerFamily D s z, t.length ≤ SieveBoxLength.cutoff s) := by
  constructor <;> intro t ht
  · exact ((SieveBoxedFamily.mem_boundedTuples _ _ _).mp (Finset.mem_filter.mp ht).1).1
  · exact ((SieveBoxedFamily.mem_boundedTuples _ _ _).mp (Finset.mem_filter.mp ht).1).1

theorem lower_coefficient_abs_le (D s z : ℝ) (m : ℕ) (hm : m ≠ 0) :
    |SieveBoxedWindow.coefficient D s z m| ≤
      2 * ((SieveBoxLength.cutoff s + 2 : ℕ) : ℝ) *
        (m.divisors.card : ℝ) ^ (SieveBoxLength.cutoff s + 1) := by
  apply signedCoefficient_abs_le _
    (SieveSmallWeights.weight (D^s) (D^(s^2)) false)
    (SieveSmallWeights.weight (D^s) (D^(s^2)) true) _ _ _ m hm
    (lower_lengths D s z).1 (lower_lengths D s z).2
  · intro d _
    exact SieveSmallWeights.weight_abs_le_one _ _ _ d
  · intro d _
    exact SieveSmallWeights.weight_abs_le_one _ _ _ d

theorem upper_coefficient_abs_le (D s z : ℝ) (m : ℕ) (hm : m ≠ 0) :
    |SieveUpperBoxWindow.coefficient D s z m| ≤
      2 * ((SieveBoxLength.cutoff s + 2 : ℕ) : ℝ) *
        (m.divisors.card : ℝ) ^ (SieveBoxLength.cutoff s + 1) := by
  apply signedCoefficient_abs_le _
    (SieveSmallWeights.weight (D^s) (D^(s^2)) true)
    (SieveSmallWeights.weight (D^s) (D^(s^2)) false) _ _ _ m hm
    (upper_lengths D s z).1 (upper_lengths D s z).2
  · intro d _
    exact SieveSmallWeights.weight_abs_le_one _ _ _ d
  · intro d _
    exact SieveSmallWeights.weight_abs_le_one _ _ _ d

/-- One eventual threshold works for both actual signed families at every
level and prime cutoff. The fixed s is chosen before that threshold. -/
theorem eventually_actual_coefficient_cap (s ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop, 1 ≤ X ∧ ∀ (D z : ℝ) (m : ℕ),
      m ≠ 0 → (m : ℝ) ≤ X^(2 : ℕ) →
      |SieveBoxedWindow.coefficient D s z m| ≤ X^ε ∧
      |SieveUpperBoxWindow.coefficient D s z m| ≤ X^ε := by
  filter_upwards [eventually_signedCoefficient_cap (SieveBoxLength.cutoff s) ε hε] with X hX
  refine ⟨hX.1, ?_⟩
  intro D z m hm hmX
  constructor
  · apply hX.2 _ (SieveSmallWeights.weight (D^s) (D^(s^2)) false)
      (SieveSmallWeights.weight (D^s) (D^(s^2)) true) _ _ m hm hmX
      (lower_lengths D s z).1 (lower_lengths D s z).2
    · intro d _
      exact SieveSmallWeights.weight_abs_le_one _ _ _ d
    · intro d _
      exact SieveSmallWeights.weight_abs_le_one _ _ _ d
  · apply hX.2 _ (SieveSmallWeights.weight (D^s) (D^(s^2)) true)
      (SieveSmallWeights.weight (D^s) (D^(s^2)) false) _ _ m hm hmX
      (upper_lengths D s z).1 (upper_lengths D s z).2
    · intro d _
      exact SieveSmallWeights.weight_abs_le_one _ _ _ d
    · intro d _
      exact SieveSmallWeights.weight_abs_le_one _ _ _ d

run_cmd do
  for decl in [``lower_lengths, ``upper_lengths, ``lower_coefficient_abs_le,
      ``upper_coefficient_abs_le, ``eventually_actual_coefficient_cap] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ALL-LENGTH BOXED COEFFICIENT CAPS PASSED"

end PositiveSharpRemainderAnalysisBoxed
