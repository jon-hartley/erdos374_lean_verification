import Item2ClosureWork
import Item1OriginalEndpointBridge

/-! Combine the independently developed item-1 and item-2 estimates at the
original literal endpoint. No remaining analytic hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Erdos374CompleteWork

theorem conclusions :
    Erdos374.MainStatement ∧
      Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
      ∃ c : ℝ, 0 < c ∧ ∃ cutoff : ℕ, ∀ N : ℕ, cutoff ≤ N →
        c*(N:ℝ) ≤ (Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  exact Item2ClosureWork.erdos_conclusions_of_item1 1
    Item1OriginalEndpointBridge.original_source_mean

theorem erdos374 : Erdos374.MainStatement := conclusions.1

theorem positive_lower_density :
    Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix := conclusions.2.1

theorem linear_count :
    ∃ c : ℝ, 0 < c ∧ ∃ cutoff : ℕ, ∀ N : ℕ, cutoff ≤ N →
      c*(N:ℝ) ≤ (Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) :=
  conclusions.2.2

#print axioms conclusions
#print axioms erdos374
#print axioms positive_lower_density
#print axioms linear_count

run_cmd do
  for decl in [``conclusions, ``erdos374, ``positive_lower_density, ``linear_count] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ERDOS 374 COMPLETE: ITEMS 1 AND 2 MERGED; NO REMAINING ANALYTIC HYPOTHESES"
end Erdos374CompleteWork
