import FrontierSieveEnumeration
import FrontierSieveCovered
import FrontierProfileClassification

/-! The literal source remainder is the checked covered sum, an explicitly
classified exceptional sum, and the empty-profile term, with original signs. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace FrontierSieveDecomposition
open FrontierSieveEnumeration SieveBoxGrouping

def exceptionalFamily (X s:ℝ) : Finset TailSieveCovered.Index :=
  allFamily X s \ FrontierSieveCovered.family X s

def exceptionalRemainder (X s z L R:ℝ) : ℝ :=
  ∑a∈exceptionalFamily X s,term X s z L R a

theorem covered_subset_all (X s:ℝ) : FrontierSieveCovered.family X s ⊆ allFamily X s := by
  intro a ha
  exact (mem_allFamily_iff X s a).mpr ((FrontierSieveCovered.mem_family_iff X s a).mp ha).2.1

theorem covered_eq_sum (X s z L R:ℝ) :
    FrontierSieveCovered.remainder X s z L R =
      ∑a∈FrontierSieveCovered.family X s,term X s z L R a := by
  simp only [FrontierSieveCovered.remainder,FiniteDivisorFamily.remainder_eq_sum,
    FrontierSieveCovered.component_remainder,term]

theorem nonempty_eq_covered_add_exceptional (X s z L R:ℝ) :
    nonemptyRemainder X s z L R =
      FrontierSieveCovered.remainder X s z L R + exceptionalRemainder X s z L R := by
  rw [covered_eq_sum]
  dsimp [nonemptyRemainder,exceptionalRemainder,exceptionalFamily]
  simpa only [add_comm] using
    (Finset.sum_sdiff (f:=term X s z L R) (covered_subset_all X s)).symm

theorem source_eq_covered_add_exceptional_sub_empty (X s z L R:ℝ)
    (hD:1<SieveWeightedCutoffs.level X s) (hs:0<s)
    (hz:z≤SieveWeightedCutoffs.level X s) :
    SieveBoxedWindow.sourceRemainder (SieveWeightedCutoffs.level X s) s z L R =
      FrontierSieveCovered.remainder X s z L R + exceptionalRemainder X s z L R -
        emptyRemainder X s z L R := by
  rw [source_eq_nonempty_sub_empty X s z L R hD hs hz,
    nonempty_eq_covered_add_exceptional]

theorem exceptional_length_lt_four (X s:ℝ) (hX:1<X) (hs:0<s) (hs1:s≤1/1000)
    (a:TailSieveCovered.Index) (ha:a∈exceptionalFamily X s) :
    (a.2.1++[a.2.2]).length<4 := by
  obtain ⟨hall,hnot⟩ := Finset.mem_sdiff.mp ha
  have hp := (mem_allFamily_iff X s a).mp hall
  apply Nat.lt_of_not_ge
  intro hlen
  exact hnot (FrontierSieveCovered.old_family_subset X s hX.le
    (FrontierProfileClassification.long_profile_mem_covered
      X s hX hs hs1 a.1 a.2.1 a.2.2 hp hlen))

theorem exceptional_cases (X s:ℝ) (hX:1<X) (hs:0<s) (hs1:s≤1/1000)
    (a:TailSieveCovered.Index) (ha:a∈exceptionalFamily X s) :
    (a.1=false ∧ a.2.1=[]) ∨
    ((a.1=true ∧ a.2.1.length=1 ∨ a.1=false ∧ a.2.1.length=2) ∧
      X^(8/35:ℝ)<SieveGeometricGrid.scale (SieveWeightedCutoffs.level X s) s (a.2.2+1)) := by
  have hlen := exceptional_length_lt_four X s hX hs hs1 a ha
  obtain ⟨hall,hnot⟩ := Finset.mem_sdiff.mp ha
  have hp := (mem_allFamily_iff X s a).mp hall
  have htest := ((mem_profiles _ _ _ _).mp hp).2.2
  simp only [List.length_append,List.length_singleton] at hlen
  by_cases hnil:a.2.1=[]
  · left
    refine ⟨?_,hnil⟩
    cases hb:a.1
    · rfl
    · simp [profileTest,hb,hnil] at htest
  · right
    have hband : X^(8/35:ℝ)<SieveGeometricGrid.scale
        (SieveWeightedCutoffs.level X s) s (a.2.2+1) := by
      apply lt_of_not_ge
      intro hb
      exact hnot ((FrontierSieveCovered.mem_family_iff X s a).mpr ⟨hnil,hp,hb⟩)
    refine ⟨?_,hband⟩
    cases hb:a.1
    · right
      refine ⟨rfl,?_⟩
      have he : ¬Even (a.2.1++[a.2.2]).length := by
        simp only [profileTest,hb,Bool.false_eq_true,ite_false] at htest
        exact htest.1
      rw [Nat.even_iff] at he
      simp only [List.length_append,List.length_singleton] at he
      have hnlen : a.2.1.length≠0 := by
        intro hz
        exact hnil (List.length_eq_zero_iff.mp hz)
      omega
    · left
      refine ⟨rfl,?_⟩
      have he : Even (a.2.1++[a.2.2]).length := by
        simp only [profileTest,hb,ite_true] at htest
        exact htest.1
      rw [Nat.even_iff] at he
      simp only [List.length_append,List.length_singleton] at he
      omega

run_cmd do
  for decl in [``covered_subset_all,``covered_eq_sum,``nonempty_eq_covered_add_exceptional,
      ``source_eq_covered_add_exceptional_sub_empty,``exceptional_length_lt_four,
      ``exceptional_cases] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT SOURCE SPLIT WITH ONLY SINGLETON AND HIGH-BAND TWO/THREE EXCEPTIONS PASSED"

end FrontierSieveDecomposition
