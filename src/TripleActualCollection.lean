import TripleActualGrouping

/-! Exact finite collection of every actual remaining outer profile.
Coincident physical divisors retain the sum of all signed profile weights. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TripleActualCollection

def componentSupport (X s z : ℝ) (a : TailSieveCovered.Index) : Finset ℕ :=
  TripleActualGrouping.support X s z a.2.1 a.2.2

def componentWeight (X s z : ℝ) (a : TailSieveCovered.Index) : ℕ → ℝ :=
  TripleActualGrouping.coefficient X s z true a.2.1 a.2.2

def support (X s z : ℝ) : Finset ℕ :=
  FiniteDivisorFamily.support (PairActualResidual.family X s) (componentSupport X s z)

def coefficient (X s z : ℝ) : ℕ → ℝ :=
  FiniteDivisorFamily.coefficient (PairActualResidual.family X s)
    (componentSupport X s z) (componentWeight X s z)

def remainder (X s z L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder (support X s z) (coefficient X s z) L R

theorem component_remainder (X s z L R : ℝ) (a : TailSieveCovered.Index) :
    HarmanDivisorWindow.remainder (componentSupport X s z a) (componentWeight X s z a) L R =
      TripleActualGrouping.remainder X s z true a.2.1 a.2.2 L R := rfl

theorem remainder_eq_actual (X s z L R : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000) :
    remainder X s z L R=PairActualResidual.remainder X s z L R := by
  rw [remainder,support,coefficient,FiniteDivisorFamily.remainder_eq_sum]
  simp_rw [component_remainder]
  exact (TripleActualGrouping.actual_remainder_eq_sum X s z L R hX hs hs1).symm

theorem family_subset_candidates (X s : ℝ) :
    PairActualResidual.family X s ⊆ TailSieveCovered.candidates s := by
  intro a ha
  have h1 := (Finset.mem_sdiff.mp ha).1
  have h2 := (Finset.mem_sdiff.mp h1).1
  have h3 := (Finset.mem_sdiff.mp h2).1
  exact (Finset.mem_filter.mp h3).1

run_cmd do
  for decl in [``component_remainder,``remainder_eq_actual,``family_subset_candidates] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL OUTER-PROFILE FINITE COLLECTION IDENTITY"

end TripleActualCollection
