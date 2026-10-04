import PairActualCollection

/-! Exact separation of the pair collection from the remaining low-d residual.
The only remaining profile sector is outer length three. No pair estimate is
assumed or asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PairActualResidual

def family (X s : ℝ) : Finset TailSieveCovered.Index :=
  SingletonActualResidual.family X s \ PairActualGeometry.sector X s

def remainder (X s z L R : ℝ) : ℝ :=
  ∑a∈family X s,(if a.1 then -1 else 1)*
    FrontierSmallBracketSplit.lowRemainder X s z (!a.1) (a.2.1++[a.2.2]) L R

theorem remaining_eq_pair_add_outer (X s z L R : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hz : z≤SieveWeightedCutoffs.level X s) :
    SingletonActualResidual.remainder X s z L R =
      PairActualCollection.remainder X s z L R+remainder X s z L R := by
  rw [PairActualCollection.remainder_eq_sector X s z L R hX hs hs1 hz]
  unfold SingletonActualResidual.remainder remainder family
  simpa only [add_comm] using (Finset.sum_sdiff
    (f:=fun a : TailSieveCovered.Index => (if a.1 then (-1:ℝ) else 1)*
      FrontierSmallBracketSplit.lowRemainder X s z (!a.1) (a.2.1++[a.2.2]) L R)
    (PairActualGeometry.sector_subset X s)).symm

theorem source_exact (X s z L R : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤SieveWeightedCutoffs.level X s) :
    SieveBoxedWindow.sourceRemainder (SieveWeightedCutoffs.level X s) s z L R =
      FrontierSieveCovered.remainder X s z L R+FrontierResidual.highRemainder X s z L R+
      SingletonActualCollection.remainder X s z L R+PairActualCollection.remainder X s z L R+
      remainder X s z L R-FrontierSieveEnumeration.emptyRemainder X s z L R := by
  have hD : 1<SieveWeightedCutoffs.level X s := Real.one_lt_rpow hX (by linarith)
  rw [SingletonActualResidual.source_exact X s z L R hD hs hz,
    remaining_eq_pair_add_outer X s z L R hX hs hs1 hz]
  ring

theorem remaining_cases (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (a : TailSieveCovered.Index) (ha : a∈family X s) :
    a.1=false ∧ a.2.1.length=2 ∧
      X^(8/35:ℝ)<SieveGeometricGrid.scale (SieveWeightedCutoffs.level X s) s (a.2.2+1) := by
  obtain ⟨ha,hn⟩ := Finset.mem_sdiff.mp ha
  obtain ⟨hcases,hscale⟩ := SingletonActualResidual.remaining_cases X s hX hs hs1 a ha
  rcases hcases with hp | ho
  · exact False.elim (hn (Finset.mem_filter.mpr ⟨ha,hp⟩))
  · exact ⟨ho.1,ho.2,hscale⟩

theorem remainder_eq_outer (X s z L R : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000) :
    remainder X s z L R = ∑a∈family X s,
      FrontierSmallBracketSplit.lowRemainder X s z true (a.2.1++[a.2.2]) L R := by
  apply Finset.sum_congr rfl
  intro a ha
  have hb := (remaining_cases X s hX hs hs1 a ha).1
  simp only [hb,Bool.false_eq_true,ite_false,Bool.not_false,one_mul]

theorem unit_mem_representations (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (t : List ℕ) (ht : t∈PairActualGeometry.tuples X s z) :
    (1,t)∈PairActualCollection.representations X s z :=
  Finset.mem_product.mpr ⟨SingletonActualResidual.one_mem_lowSupport X s hX hs hs1,ht⟩

theorem unit_summand (X s : ℝ) : -FrontierSmallBracket.smallWeight X s false 1 = -1 := by
  simp only [FrontierSmallBracket.smallWeight,SieveSmallWeights.weight_one]

run_cmd do
  for decl in [``remaining_eq_pair_add_outer,``source_exact,``remaining_cases,
      ``remainder_eq_outer,``unit_mem_representations,``unit_summand] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL PAIR REMOVED ALGEBRAICALLY; OUTER TRIPLES AND UNIT TERMS RETAINED"

end PairActualResidual
