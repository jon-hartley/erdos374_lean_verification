import FrontierSieveDecomposition
import FrontierSmallBracketSplit
import FrontierSmallBracketCovered

/-! Exact remaining source after two disjoint proved contributions are removed.
The still-open exceptional contribution uses only low small-divisor indices. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace FrontierResidual
open FrontierSieveEnumeration FrontierSieveDecomposition

def profileIndex (a:TailSieveCovered.Index) : FrontierSmallBracketCovered.Index :=
  (a.1,a.2.1++[a.2.2])

theorem profileIndex_injective : Function.Injective profileIndex := by
  intro a b hab
  exact Prod.ext (congrArg (fun p:FrontierSmallBracketCovered.Index => p.1) hab)
    (TailSieveCovered.snoc_injective
      (congrArg (fun p:FrontierSmallBracketCovered.Index => p.2) hab))

def highFamily (X s:ℝ) : Finset FrontierSmallBracketCovered.Index :=
  (exceptionalFamily X s).image profileIndex

def highRemainder (X s z L R:ℝ) : ℝ :=
  FrontierSmallBracketCovered.remainder X s z (highFamily X s) L R

def lowRemainder (X s z L R:ℝ) : ℝ :=
  ∑a∈exceptionalFamily X s, (if a.1 then -1 else 1)*
    FrontierSmallBracketSplit.lowRemainder X s z (!a.1) (a.2.1++[a.2.2]) L R

theorem highFamily_subset (X s:ℝ) :
    highFamily X s ⊆ FrontierSmallBracketCovered.family X s := by
  intro b hb
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  apply (FrontierSmallBracketCovered.mem_family_iff X s _).mpr
  refine ⟨by simp [profileIndex],?_⟩
  exact (mem_allFamily_iff X s a).mp (Finset.mem_sdiff.mp ha).1

theorem high_eq_sum (X s z L R:ℝ) :
    highRemainder X s z L R = ∑a∈exceptionalFamily X s,
      (if a.1 then -1 else 1)*
        FrontierSmallBracket.remainder X s z (!a.1) (a.2.1++[a.2.2]) L R := by
  rw [highRemainder,FrontierSmallBracketCovered.remainder_eq_sum,highFamily,
    Finset.sum_image (fun a _ b _ hab => profileIndex_injective hab)]
  rfl

theorem exceptional_eq_high_add_low (X s z L R:ℝ) :
    exceptionalRemainder X s z L R=highRemainder X s z L R+lowRemainder X s z L R := by
  simp only [exceptionalRemainder,term,FrontierSmallBracketSplit.snoc_remainder_split,
    mul_add,Finset.sum_add_distrib,high_eq_sum,lowRemainder]

theorem source_exact (X s z L R:ℝ) (hD:1<SieveWeightedCutoffs.level X s)
    (hs:0<s) (hz:z≤SieveWeightedCutoffs.level X s) :
    SieveBoxedWindow.sourceRemainder (SieveWeightedCutoffs.level X s) s z L R =
      FrontierSieveCovered.remainder X s z L R + highRemainder X s z L R +
        lowRemainder X s z L R - emptyRemainder X s z L R := by
  rw [source_eq_covered_add_exceptional_sub_empty X s z L R hD hs hz,
    exceptional_eq_high_add_low]
  ring

theorem low_profile_cases (X s:ℝ) (hX:1<X) (hs:0<s) (hs1:s≤1/1000)
    (a:TailSieveCovered.Index) (ha:a∈exceptionalFamily X s) :
    (a.1=false ∧ a.2.1=[]) ∨
    ((a.1=true ∧ a.2.1.length=1 ∨ a.1=false ∧ a.2.1.length=2) ∧
      X^(8/35:ℝ)<SieveGeometricGrid.scale (SieveWeightedCutoffs.level X s) s (a.2.2+1)) :=
  exceptional_cases X s hX hs hs1 a ha

theorem eventually_high_half_width_bound (s:ℝ) (hs:0<s) (hs1:s≤1/1000) :
    ∃c:ℝ, 0<c ∧ ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀z:ℝ,
      z≤SieveWeightedCutoffs.level X s →
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),highRemainder X s z (x-x*(Y/X)) x ^2)≤Y^2*X^(-c) := by
  obtain ⟨c,hc,he⟩ := FrontierSmallBracketCovered.eventually_half_width_bound s hs hs1
  refine ⟨c,hc,?_⟩
  filter_upwards [he] with X hh
  exact ⟨hh.1,fun z hz => hh.2 z (highFamily X s) hz (highFamily_subset X s)⟩

run_cmd do
  for decl in [``profileIndex_injective,``highFamily_subset,``high_eq_sum,
      ``exceptional_eq_high_add_low,``source_exact,``low_profile_cases,
      ``eventually_high_half_width_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT LOWER SOURCE REDUCED TO LOW-D SINGLETON AND HIGH-BAND SHORT PROFILES"

end FrontierResidual
