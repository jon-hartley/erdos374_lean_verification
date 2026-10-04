import LongPairEdgeProfileMeanWork
import ProductHighMasksWork

/-! Exact original high-product large-band pair profiles with selected
prime q≤X^.229. The physical lower product cutoff is kept in the masks. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairEdgeHighProfileMeanWork
open LongPairEdgeProfileMeanWork ProductHighMasksWork ProductCappedMasksWork
open LongPairProfilesWork ShortPairSplitWork LongerTupleActualProfiles
open LongPairSmallProfileMeanWork SieveWeightedCutoffs PositiveSharpBoxedCount
open LongerTupleProfile ShortSingletonMasks ShortSingletonEndpoints UpperAfter545Remaining
open SieveGeometricGrid

def highCut (X : ℝ) (m : ℕ) : ℕ :=
  max (physicalCut X m) (upperEndpoint (X^(26/35:ℝ)) m)

def highRelation (X s : ℝ) (second : Bool) (js : List ℕ) (m q : ℕ) : Prop :=
  completionRelation X s (largePrimes X) (cutoffThree X s) second js m q ∧
    X^(26/35:ℝ)<((m*q:ℕ):ℝ)

def edgeHighKernel (X s : ℝ) (second : Bool) (js : List ℕ) (L R : ℝ) : ℂ :=
  ∑ r∈pairSource X s (largePrimes X) (cutoffThree X s) second js,
    if (prime second r:ℝ)≤X^(229/1000:ℝ) ∧
        X^(26/35:ℝ)<(LongerTupleEncoding.index r:ℝ) then
      originalWeight X s true r*(floorKernel L R (LongerTupleEncoding.index r):ℂ) else 0

def edgeHighMaskedSum (X s : ℝ) (second : Bool) (js : List ℕ) (L R : ℝ) : ℂ :=
  LongerTupleMaskedCollection.maskedSum
    (pairSupport X s (largePrimes X) (cutoffThree X s) second js)
    ShortPairSplitWork.index (edgePrimes X) (pairWeight X s)
    (pairLo X s second js) (pairHi X s (cutoffThree X s) second js) (highCut X) L R

theorem kernel_eq_masked (X s : ℝ) (second : Bool) (js : List ℕ) (hjs : js.length=2)
    (hX : 1<X) (hs : 0<s) (hg : BandGeometry X s (largePrimes X) (cutoffThree X s))
    (L R : ℝ) : edgeHighKernel X s second js L R=edgeHighMaskedSum X s second js L R := by
  unfold edgeHighKernel
  rw [completion_sum second _ (longPrimeSupport X)
    (pairSource_length X s _ _ second js hjs)
    (pairSource_prime_mem X s _ _ second js hjs hX.le hs hg)]
  unfold edgeHighMaskedSum LongerTupleMaskedCollection.maskedSum edgePrimes highCut
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro q hq
  rw [high_mask (X^(26/35:ℝ)) (ShortPairSplitWork.index a) _ _ _ q
    (by positivity) (pairSupport_index_pos X s _ _ second js hjs (by linarith) a ha)]
  have hcomp := LongPairProfilesWork.completion_iff X s _ _ second js hjs
    (by linarith) hs hg a ha q hq
  have hp : a.1∈largePrimes X := by
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp ha
    rw [←he]
    exact ((mem_source X s _ _ true js r).mp (Finset.mem_filter.mp hr).1).1
  have hgeom := hg a.1 hp
  have he := box_pool_high_prefix X (level X s/a.1) s (cutoffThree X s a.1)
    (selectedIndex second js) (ShortPairSplitWork.index a) q (by linarith)
    (by linarith [hgeom.2.2.1])
    (pairSupport_cutoff_pos X s _ _ second js hjs hs hg a ha)
    (pairSupport_index_pos X s _ _ second js hjs (by linarith) a ha)
  simp only [hcomp,prime_rebuild,ShortPairSplitWork.index_rebuild,pairHi,pairLo]
  rw [←he]
  by_cases hc : InBox (level X s/a.1) s (q:ℝ) (selectedIndex second js) ∧
      (q:ℝ)<cutoffThree X s a.1 ∧ X^(109/200:ℝ)<((ShortPairSplitWork.index a*q:ℕ):ℝ) <;>
    by_cases hu : (q:ℝ)≤X^(229/1000:ℝ) <;>
    by_cases hh : X^(26/35:ℝ)<((ShortPairSplitWork.index a*q:ℕ):ℝ) <;>
      simp only [hc,hu,hh,ite_true,ite_false,originalWeight,pairWeight,rebuild,
        and_true,and_false,mul_zero,zero_mul,mul_one]

theorem eventually_edgeHigh_square (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ (second : Bool) (js : List ℕ), js.length=2 →
        let Y : ℝ := X^(101/1000:ℝ)/2
        (1/X)*(∫ x in Icc X (2*X),
          (edgeHighKernel X s second js (x-x*(Y/X)) x).re^2)≤Y^2*X^(-c) := by
  obtain ⟨c,hc,hmean⟩ := LongPairEdgeGlobalMeanWork.eventually_bound (α:=PairRep) 3
  refine ⟨c,hc,?_⟩
  filter_upwards [hmean,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1000)] with X hm hX hlog
  refine ⟨hX,hlog,?_⟩
  intro second js hjs
  dsimp only
  let P := largePrimes X
  let z := cutoffThree X s
  have hg : BandGeometry X s P z := large_band_geometry X s hX hs hs1 hlog
  have hB (q : ℕ) (hq : q∈edgePrimes X) :=
    (mem_longPrimeSupport X q (by linarith)).mp (Finset.mem_filter.mp hq).1
  have hb := hm.2 (pairSupport X s P z second js) ShortPairSplitWork.index ShortPairSplitWork.encode
    (edgePrimes X) (highRelation X s second js) (Nat.floor X) (pairWeight X s)
    (pairLo X s second js) (pairHi X s z second js) (highCut X)
    (fun a _ => ShortPairSplitWork.encode_product a)
    (fun a _ b _ he => ShortPairSplitWork.encode_injective he)
    (by intro m hm; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
        exact support_bounds X s P z second js hjs hX hs hs1 hg a ha)
    (fun q hq => ⟨(hB q hq).1.two_le,(hB q hq).2.2⟩)
    (fun q hq => (Nat.le_floor_iff (by linarith : 0≤X)).mpr (hB q hq).2.2)
    (Nat.floor_le (by linarith : 0≤X))
    (by intro a _; rw [pairWeight,Complex.norm_real,Real.norm_eq_abs]
        exact SieveSmallWeights.weight_abs_le_one _ _ true a.2.1)
    (by intro m _ q hq hr
        obtain ⟨⟨a,ha,he,hr⟩,_⟩ := hr
        have hsource := source_in_collection X s P z second js hjs _ hr
        have hphysical := ((LongPairCollectionWork.mem_source X s P z _).mp hsource).2.2.2.2.2
        have hupper := LongPairLargeGeometryWork.large_source_upper X s hX hs hs1 hlog _ hsource
        rw [ShortPairSplitWork.index_rebuild,he,Nat.cast_mul] at hphysical hupper
        exact ⟨by simpa only [show (545/1000:ℝ)=109/200 by norm_num] using hphysical.le,
          (hB q hq).2.1.le,(Finset.mem_filter.mp hq).2,
          hupper.le.trans (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith))⟩)
    (by intro a ha q hq hn
        unfold highCut
        rw [high_mask (X^(26/35:ℝ)) (ShortPairSplitWork.index a) _ _ _ q
          (by positivity) (pairSupport_index_pos X s P z second js hjs (by linarith) a ha)]
        by_cases hh : X^(26/35:ℝ)<((ShortPairSplitWork.index a*q:ℕ):ℝ)
        · simp only [hh,ite_true]
          exact mask_zero X s P z second js hjs hX hs hg a ha q
            (Finset.mem_filter.mp hq).1 (fun hc => hn ⟨hc,hh⟩)
        · simp only [hh,ite_false])
  change (1/X)*(∫ x in Icc X (2*X),
    (edgeHighMaskedSum X s second js (x-x*((X^(101/1000:ℝ)/2)/X)) x).re^2)≤_ at hb
  simp_rw [←kernel_eq_masked X s second js hjs hX hs hg] at hb
  exact hb

#print axioms eventually_edgeHigh_square
run_cmd do
  for decl in [``kernel_eq_masked, ``eventually_edgeHigh_square] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairEdgeHighProfileMeanWork
