import SingletonActualCollection

/-! Removing precisely the collected singleton leaves the actual low-d inner
pair and outer triple sectors. This is an identity, not their analytic bound. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SingletonActualResidual
open SingletonActualCollection

def family (X s : ℝ) : Finset TailSieveCovered.Index :=
  FrontierSieveDecomposition.exceptionalFamily X s \ sector X s

def remainder (X s z L R : ℝ) : ℝ :=
  ∑a∈family X s,(if a.1 then -1 else 1)*
    FrontierSmallBracketSplit.lowRemainder X s z (!a.1) (a.2.1++[a.2.2]) L R

theorem sector_subset (X s : ℝ) :
    sector X s ⊆ FrontierSieveDecomposition.exceptionalFamily X s :=
  Finset.filter_subset _ _

theorem low_eq_singleton_add_remaining (X s z L R : ℝ) :
    FrontierResidual.lowRemainder X s z L R =
      SingletonActualCollection.remainder X s z L R + remainder X s z L R := by
  rw [SingletonActualCollection.remainder_eq_sector]
  unfold FrontierResidual.lowRemainder remainder family
  simpa only [add_comm] using (Finset.sum_sdiff
    (f:=fun a : TailSieveCovered.Index => (if a.1 then (-1:ℝ) else 1)*
      FrontierSmallBracketSplit.lowRemainder X s z (!a.1) (a.2.1++[a.2.2]) L R)
    (sector_subset X s)).symm

theorem source_exact (X s z L R : ℝ) (hD : 1<SieveWeightedCutoffs.level X s)
    (hs : 0<s) (hz : z≤SieveWeightedCutoffs.level X s) :
    SieveBoxedWindow.sourceRemainder (SieveWeightedCutoffs.level X s) s z L R =
      FrontierSieveCovered.remainder X s z L R + FrontierResidual.highRemainder X s z L R +
      SingletonActualCollection.remainder X s z L R + remainder X s z L R -
        FrontierSieveEnumeration.emptyRemainder X s z L R := by
  rw [FrontierResidual.source_exact X s z L R hD hs hz,low_eq_singleton_add_remaining]
  ring

theorem remaining_cases (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (a : TailSieveCovered.Index) (ha : a∈family X s) :
    ((a.1=true ∧ a.2.1.length=1) ∨ (a.1=false ∧ a.2.1.length=2)) ∧
      X^(8/35:ℝ)<SieveGeometricGrid.scale (SieveWeightedCutoffs.level X s) s (a.2.2+1) := by
  obtain ⟨ha,hn⟩ := Finset.mem_sdiff.mp ha
  rcases FrontierResidual.low_profile_cases X s hX hs hs1 a ha with hsingle | hother
  · exact False.elim (hn (Finset.mem_filter.mpr ⟨ha,hsingle⟩))
  · exact hother

theorem one_mem_lowSupport (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000) :
    1∈FrontierSmallBracketSplit.lowSupport X s := by
  apply (FrontierSmallBracketSplit.mem_lowSupport X s 1).mpr
  constructor
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨∅,SievePrefix.empty_mem_selected _ false 1 _,by simp [SievePrimeSubset.subsetProduct]⟩
  · simpa using Real.one_lt_rpow hX
      (FourPrimeScaleBudget.lowerExponent_pos s hs (by linarith))

theorem prime_coefficient_one (X s z : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hz : z≤SieveWeightedCutoffs.level X s)
    (j p : ℕ) (hj : j∈bands X s)
    (hp : p∈SieveBoxGrouping.primeBand (SieveWeightedCutoffs.level X s) s z j) :
    coefficient X s z p=1 := by
  have ha : (j,1,p)∈representations X s z :=
    (mem_representations X s z _).mpr ⟨hj,one_mem_lowSupport X s hX hs hs1,hp⟩
  have he := coefficient_at_index X s z hX hs hs1 hz (j,1,p) ha
  simpa [index,FrontierSmallBracket.smallWeight,SieveSmallWeights.weight_one] using he

run_cmd do
  for decl in [``sector_subset,``low_eq_singleton_add_remaining,``source_exact,``remaining_cases,
      ``one_mem_lowSupport,``prime_coefficient_one] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SINGLETON EXACTLY REMOVED FROM LOW-D RESIDUAL; UNIT TERM RETAINED"

end SingletonActualResidual
