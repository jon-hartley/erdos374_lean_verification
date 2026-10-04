import TailSieveCovered

/-! Exact enumeration of every nonempty lower-sieve profile by its final band.
The empty inner profile is kept as a separate, signed term. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace FrontierSieveEnumeration
open SieveBoxGrouping

def pairs (s:ℝ) : Finset (List ℕ × ℕ) :=
  SieveBoxedFamily.boundedTuples (Finset.range (SieveGeometricGrid.cutoff s+1))
    (SieveBoxLength.cutoff s) ×ˢ Finset.range (SieveGeometricGrid.cutoff s+1)

def pairFamily (positive:Bool) (D s:ℝ) : Finset (List ℕ × ℕ) :=
  (pairs s).filter (fun a => a.1++[a.2]∈profiles positive D s)

def allFamily (X s:ℝ) : Finset TailSieveCovered.Index :=
  (TailSieveCovered.candidates s).filter (fun a =>
    a.2.1++[a.2.2]∈profiles a.1 (SieveWeightedCutoffs.level X s) s)

theorem pair_mem_of_profile (positive:Bool) (D s:ℝ) (a:List ℕ×ℕ)
    (ha:a.1++[a.2]∈profiles positive D s) : a∈pairFamily positive D s := by
  obtain ⟨hlen,hindices,_⟩ := (mem_profiles _ _ _ _).mp ha
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,ha⟩
  · apply (SieveBoxedFamily.mem_boundedTuples _ _ _).mpr
    refine ⟨?_,?_⟩
    · simp only [List.length_append,List.length_singleton] at hlen
      omega
    · intro i hi
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        (hindices i (List.mem_append_left _ hi)))
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hindices _ (by simp)))

theorem mem_allFamily_iff (X s:ℝ) (a:TailSieveCovered.Index) :
    a∈allFamily X s ↔ a.2.1++[a.2.2]∈profiles a.1 (SieveWeightedCutoffs.level X s) s := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    have hp := (Finset.mem_filter.mp (pair_mem_of_profile _ _ _ a.2 h)).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,hp⟩,h⟩

theorem sum_nonempty_profiles (positive:Bool) (D s:ℝ) (f:List ℕ→ℝ) :
    (∑a∈pairFamily positive D s, f (a.1++[a.2])) =
      ∑g∈(profiles positive D s).erase [], f g := by
  apply Finset.sum_bij (fun a _ => a.1++[a.2])
  · intro a ha
    exact Finset.mem_erase.mpr ⟨by simp,(Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ hab
    exact TailSieveCovered.snoc_injective hab
  · intro g hg
    obtain ⟨hgnil,hg⟩ := Finset.mem_erase.mp hg
    refine ⟨(g.dropLast,g.getLast hgnil),?_,List.dropLast_append_getLast hgnil⟩
    apply pair_mem_of_profile
    simpa only [List.dropLast_append_getLast hgnil] using hg
  · intro a _
    rfl

def cut (g:List ℕ) : ℕ := g.length-1

theorem profile_snoc (D s z:ℝ) (upper:Bool) (g:List ℕ) (j:ℕ) (L R:ℝ) :
    MomentRemainderProfileSplit.profileRemainder D s z upper cut (g++[j]) L R =
      TailSieveProfileBasics.remainder D s z upper g j L R := by
  rw [TailSieveProfileBasics.remainder_eq_profile]
  simp only [MomentRemainderProfileSplit.profileRemainder,cut,
    List.length_append,List.length_singleton,Nat.add_sub_cancel]

def term (X s z L R:ℝ) (a:TailSieveCovered.Index) : ℝ :=
  (if a.1 then -1 else 1) * TailSieveProfileBasics.remainder
    (SieveWeightedCutoffs.level X s) s z (!a.1) a.2.1 a.2.2 L R

def nonemptyRemainder (X s z L R:ℝ) : ℝ := ∑a∈allFamily X s,term X s z L R a

def emptyRemainder (X s z L R:ℝ) : ℝ :=
  MomentRemainderProfileSplit.profileRemainder
    (SieveWeightedCutoffs.level X s) s z false cut [] L R

theorem nonempty_eq_profile_sums (X s z L R:ℝ) :
    nonemptyRemainder X s z L R =
      (∑g∈(profiles false (SieveWeightedCutoffs.level X s) s).erase [],
        MomentRemainderProfileSplit.profileRemainder
          (SieveWeightedCutoffs.level X s) s z true cut g L R) -
      ∑g∈(profiles true (SieveWeightedCutoffs.level X s) s).erase [],
        MomentRemainderProfileSplit.profileRemainder
          (SieveWeightedCutoffs.level X s) s z false cut g L R := by
  simp only [nonemptyRemainder,allFamily,TailSieveCovered.candidates,
    Finset.sum_filter]
  rw [Finset.sum_product]
  change (∑b:Bool, ∑a∈pairs s,
    if a.1++[a.2]∈profiles b (SieveWeightedCutoffs.level X s) s
    then term X s z L R (b,a) else 0) = _
  simp only [Fintype.sum_bool,term,Bool.false_eq_true,ite_false,ite_true,
    Bool.not_false,Bool.not_true,one_mul,neg_one_mul]
  have hfalse := sum_nonempty_profiles false (SieveWeightedCutoffs.level X s) s
    (fun g => MomentRemainderProfileSplit.profileRemainder
      (SieveWeightedCutoffs.level X s) s z true cut g L R)
  have htrue := sum_nonempty_profiles true (SieveWeightedCutoffs.level X s) s
    (fun g => MomentRemainderProfileSplit.profileRemainder
      (SieveWeightedCutoffs.level X s) s z false cut g L R)
  simp only [pairFamily,Finset.sum_filter,profile_snoc] at hfalse htrue
  have hnegative : (∑a∈pairs s,
      if a.1++[a.2]∈profiles true (SieveWeightedCutoffs.level X s) s then
        -TailSieveProfileBasics.remainder (SieveWeightedCutoffs.level X s) s z false a.1 a.2 L R
      else 0) = -(∑a∈pairs s,
      if a.1++[a.2]∈profiles true (SieveWeightedCutoffs.level X s) s then
        TailSieveProfileBasics.remainder (SieveWeightedCutoffs.level X s) s z false a.1 a.2 L R
      else 0) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [hnegative,hfalse,htrue]
  ring

theorem source_eq_nonempty_sub_empty (X s z L R:ℝ)
    (hD:1<SieveWeightedCutoffs.level X s) (hs:0<s)
    (hz:z≤SieveWeightedCutoffs.level X s) :
    SieveBoxedWindow.sourceRemainder (SieveWeightedCutoffs.level X s) s z L R =
      nonemptyRemainder X s z L R - emptyRemainder X s z L R := by
  rw [MomentRemainderProfileSplit.source_remainder_split _ s z hD hs hz cut,
    nonempty_eq_profile_sums]
  have hout : []∉profiles false (SieveWeightedCutoffs.level X s) s := by
    simp [mem_profiles,profileTest]
  have hin := empty_mem_positive_profiles (SieveWeightedCutoffs.level X s) s
  rw [Finset.erase_eq_of_notMem hout]
  have hsum := Finset.sum_erase_add (profiles true (SieveWeightedCutoffs.level X s) s)
    (fun g => MomentRemainderProfileSplit.profileRemainder
      (SieveWeightedCutoffs.level X s) s z false cut g L R) hin
  dsimp [emptyRemainder]
  linarith

run_cmd do
  for decl in [``pair_mem_of_profile,``mem_allFamily_iff,``sum_nonempty_profiles,
      ``profile_snoc,``nonempty_eq_profile_sums,``source_eq_nonempty_sub_empty] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT NONEMPTY AND EMPTY SOURCE PROFILE ENUMERATION PASSED"

end FrontierSieveEnumeration
