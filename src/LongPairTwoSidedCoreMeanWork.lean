import LongPairFilteredEdgeFirstMeanWork
import LongPairHighCoreMeanWork
import LongPairHighStripWork
import LongPairSmallMeanWork

/-! Remove the first-prime edge from the existing second-prime core.
The filtered edge mean is proved independently; no monotonicity of
absolute remainders under source restriction is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairTwoSidedCoreMeanWork
open LongerTupleActualProfiles LongPairProfilesWork LongPairSmallProfileMeanWork
open LongPairFilteredEdgeProfileMeanWork LongPairFilteredEdgeFirstMeanWork LongPairHighStripWork
open LongPairHighCoreMeanWork
open LongPairSmallMeanWork LongerTupleHigherMeanWork LongPairLargeFlatMeanWork
open SieveWeightedCutoffs PositiveSharpBoxedCount LongerTupleProfile SieveBoxedFamily
open UpperAfter545Remaining

def otherEdgeSource (X s : ℝ) : Finset LongerTupleEncoding.Representation :=
  (LongPairHighCoreMeanWork.highCoreSource X s).filter (fun r => (ShortPairSplitWork.prime false r:ℝ)≤X^(229/1000:ℝ))
def twoSidedCoreSource (X s : ℝ) : Finset LongerTupleEncoding.Representation :=
  (LongPairHighCoreMeanWork.highCoreSource X s).filter (fun r => X^(229/1000:ℝ)<(ShortPairSplitWork.prime false r:ℝ))
def otherEdgeRemainder (X s L R : ℝ) : ℝ :=
  (∑ r∈otherEdgeSource X s,
    originalWeight X s true r*(floorKernel L R (LongerTupleEncoding.index r):ℂ)).re
def twoSidedCoreRemainder (X s L R : ℝ) : ℝ :=
  (∑ r∈twoSidedCoreSource X s,
    originalWeight X s true r*(floorKernel L R (LongerTupleEncoding.index r):ℂ)).re

theorem core_partition (X s L R : ℝ) :
    LongPairHighCoreMeanWork.highCoreRemainder X s L R=
      otherEdgeRemainder X s L R+twoSidedCoreRemainder X s L R := by
  unfold LongPairHighCoreMeanWork.highCoreRemainder
  unfold otherEdgeRemainder twoSidedCoreRemainder otherEdgeSource twoSidedCoreSource
  rw [←Complex.add_re]
  congr 1
  simp only [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hc : (ShortPairSplitWork.prime false r:ℝ)≤X^(229/1000:ℝ)
  · simp only [hc,not_lt_of_ge hc,ite_true,ite_false,add_zero]
  · simp only [hc,lt_of_not_ge hc,ite_false,ite_true,zero_add]

theorem pairSource_iff_collection (X s : ℝ) (second : Bool) (js : List ℕ) (hjs : js.length=2)
    (r : LongerTupleEncoding.Representation) :
    r∈pairSource X s (largePrimes X) (cutoffThree X s) second js ↔
      r∈LongPairCollectionWork.source X s (largePrimes X) (cutoffThree X s) ∧
        indices (level X s/r.1) s r.2.2=js := by
  constructor
  · intro hr
    exact ⟨source_in_collection X s _ _ second js hjs r hr,
      ((mem_source X s _ _ true js r).mp (Finset.mem_filter.mp hr).1).2.2.2.1⟩
  · rintro ⟨hr,he⟩
    obtain ⟨hp,hd,ht,hlen,hl,hh⟩ := (LongPairCollectionWork.mem_source X s _ _ r).mp hr
    exact Finset.mem_filter.mpr ⟨(mem_source X s _ _ true js r).mpr
      ⟨hp,hd,ht,he,hh⟩,(chosen_iff_allLong X second r hlen).mpr hl⟩

/-- On first-prime completion the original second prime is part of the
left representation, so this restriction preserves factor separation. -/
def otherKeep (X : ℝ) (a : ShortPairSplitWork.PairRep) : Prop :=
  X^(229/1000:ℝ)<(a.2.2:ℝ)

theorem otherKeep_drop (X : ℝ) (r : LongerTupleEncoding.Representation) :
    otherKeep X (ShortPairSplitWork.drop false r) ↔
      X^(229/1000:ℝ)<(ShortPairSplitWork.prime true r:ℝ) := by rfl

theorem otherEdge_eq_profiles (X s L R : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) :
    otherEdgeRemainder X s L R=∑ js∈pairProfiles s,(filteredKernel X s false js (otherKeep X) L R).re := by
  let J := pairProfiles s
  let f : LongerTupleEncoding.Representation → List ℕ :=
    fun r => indices (level X s/r.1) s r.2.2
  have hg := large_band_geometry X s hX hs hs1 hlog
  have maps : ∀ r∈otherEdgeSource X s,f r∈J := by
    intro r hr
    have hrcol := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1).1
    obtain ⟨hp,_,ht,hlen,_,_⟩ := (LongPairCollectionWork.mem_source X s _ _ r).mp hrcol
    apply Finset.mem_filter.mpr
    refine ⟨?_,by simpa only [f,indices,List.length_map] using hlen⟩
    exact ((family_fixed_iff true _ s _ (hg r.1 hp).2.2.1 hs (hg r.1 hp).2.2.2
      r.2.2 (f r)).mp ⟨ht,rfl⟩).1
  have hfiber (js : List ℕ) (hjs : js∈J) :
      (otherEdgeSource X s).filter (fun r => f r=js)=profileSource X s false js (otherKeep X) := by
    have hlen := (Finset.mem_filter.mp hjs).2
    ext r
    simp only [otherEdgeSource,LongPairHighCoreMeanWork.highCoreSource,highSource,
      profileSource,Finset.mem_filter,otherKeep_drop]
    rw [pairSource_iff_collection X s false js hlen r]
    dsimp only [f]
    tauto
  unfold otherEdgeRemainder
  rw [←Finset.sum_fiberwise_of_maps_to maps]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro js hjs
  rw [hfiber js hjs]
  unfold filteredKernel
  simp only [profileSource,Finset.sum_filter]

theorem otherEdge_moving_integrable (X s Y : ℝ) :
    IntegrableOn (fun x => otherEdgeRemainder X s (x-x*(Y/X)) x) (Icc X (2*X)) := by
  unfold otherEdgeRemainder
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  apply integrable_finsetSum
  intro r _
  have hf := TailRemainderBand.moving_remainder_integrable
    ({LongerTupleEncoding.index r}:Finset ℕ) (fun _ => (originalWeight X s true r).re) X Y
  simpa only [IntegrableOn,HarmanDivisorWindow.remainder_eq_sum,Finset.sum_singleton,floorKernel,mul_div_assoc] using hf

theorem twoSidedCore_moving_integrable (X s Y : ℝ) :
    IntegrableOn (fun x => twoSidedCoreRemainder X s (x-x*(Y/X)) x) (Icc X (2*X)) := by
  unfold twoSidedCoreRemainder
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  apply integrable_finsetSum
  intro r _
  have hf := TailRemainderBand.moving_remainder_integrable
    ({LongerTupleEncoding.index r}:Finset ℕ) (fun _ => (originalWeight X s true r).re) X Y
  simpa only [IntegrableOn,HarmanDivisorWindow.remainder_eq_sum,Finset.sum_singleton,floorKernel,mul_div_assoc] using hf

theorem eventually_otherEdge_absolute_log (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      let Y := PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X),|otherEdgeRemainder X s (x-x*(Y/X)) x|)≤
        ((pairProfiles s).card:ℝ)*Y/(Real.log X)^A := by
  filter_upwards [eventually_pair_absolute_log s A hs hs1] with X hm
  refine ⟨hm.1,hm.2.1,?_⟩
  dsimp only
  let Y := PositiveSharpPowerWindow.halfWidth X (101/1000)
  simp_rw [otherEdge_eq_profiles X s _ _ hm.1 hs hs1 hm.2.1]
  apply (absolute_sum_mean_le (pairProfiles s)
    (fun js x => (filteredKernel X s false js (otherKeep X) (x-x*(Y/X)) x).re)
    X (by linarith [hm.1]) (fun js _ => moving_integrable X s Y false js (otherKeep X))).trans
  calc
    _ ≤ ∑ js∈pairProfiles s,Y/(Real.log X)^A := Finset.sum_le_sum
      (fun js hjs => hm.2.2 false js (otherKeep X) (Finset.mem_filter.mp hjs).2)
    _ = _ := by simp; ring

theorem eventually_otherEdge_absolute_log_unit (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      let Y := PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X),|otherEdgeRemainder X s (x-x*(Y/X)) x|)≤Y/(Real.log X)^A := by
  filter_upwards [eventually_otherEdge_absolute_log s (A+1) hs hs1,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((pairProfiles s).card:ℝ)),
    PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num)] with X hm hcost hY
  refine ⟨hm.1,hm.2.1,hm.2.2.trans ?_⟩
  have hl : 0<Real.log X := Real.log_pos hm.1
  apply (div_le_div_iff₀ (pow_pos hl (A+1)) (pow_pos hl A)).mpr
  rw [pow_succ]
  have hh := mul_le_mul_of_nonneg_left hcost
    (mul_nonneg hY.1.le (pow_nonneg hl.le A))
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hh

#print axioms eventually_otherEdge_absolute_log_unit
run_cmd do
  for decl in [``core_partition, ``pairSource_iff_collection, ``otherKeep_drop, ``otherEdge_eq_profiles,
      ``otherEdge_moving_integrable, ``twoSidedCore_moving_integrable,
      ``eventually_otherEdge_absolute_log, ``eventually_otherEdge_absolute_log_unit] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairTwoSidedCoreMeanWork
