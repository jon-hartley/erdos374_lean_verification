import LongPairEdgeGlobalMeanWork
import LongPairSmallProfileMeanWork
import LongPairLargeGeometryWork

/-! Exact original large-band pair profiles restricted by the selected
prime q≤X^.229, with an unconditional square mean. Full-profile aggregation
and a complementary-strip endpoint reduction remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairEdgeProfileMeanWork
open LongPairProfilesWork ShortPairSplitWork LongerTupleActualProfiles
open LongPairSmallProfileMeanWork SieveWeightedCutoffs PositiveSharpBoxedCount
open LongerTupleProfile ShortSingletonMasks ShortSingletonEndpoints UpperAfter545Remaining
open SieveGeometricGrid

def edgePrimes (X : ℝ) : Finset ℕ :=
  (longPrimeSupport X).filter (fun q => (q:ℝ)≤X^(229/1000:ℝ))

def edgeKernel (X s : ℝ) (second : Bool) (js : List ℕ) (L R : ℝ) : ℂ :=
  ∑ r∈pairSource X s (largePrimes X) (cutoffThree X s) second js,
    if (prime second r:ℝ)≤X^(229/1000:ℝ) then
      originalWeight X s true r*(floorKernel L R (LongerTupleEncoding.index r):ℂ) else 0

def edgeMaskedSum (X s : ℝ) (second : Bool) (js : List ℕ) (L R : ℝ) : ℂ :=
  LongerTupleMaskedCollection.maskedSum
    (pairSupport X s (largePrimes X) (cutoffThree X s) second js)
    ShortPairSplitWork.index (edgePrimes X) (pairWeight X s)
    (pairLo X s second js) (pairHi X s (cutoffThree X s) second js) (physicalCut X) L R

theorem kernel_eq_masked (X s : ℝ) (second : Bool) (js : List ℕ) (hjs : js.length=2)
    (hX : 1<X) (hs : 0<s) (hg : BandGeometry X s (largePrimes X) (cutoffThree X s))
    (L R : ℝ) : edgeKernel X s second js L R=edgeMaskedSum X s second js L R := by
  unfold edgeKernel
  rw [completion_sum second _ (longPrimeSupport X)
    (pairSource_length X s _ _ second js hjs)
    (pairSource_prime_mem X s _ _ second js hjs hX.le hs hg)]
  unfold edgeMaskedSum LongerTupleMaskedCollection.maskedSum edgePrimes
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro q hq
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
      simp only [hc,hu,ite_true,ite_false,originalWeight,pairWeight,rebuild,
        and_true,mul_zero,zero_mul,mul_one]

theorem eventually_edge_square (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ (second : Bool) (js : List ℕ), js.length=2 →
        let Y : ℝ := X^(101/1000:ℝ)/2
        (1/X)*(∫ x in Icc X (2*X),
          (edgeKernel X s second js (x-x*(Y/X)) x).re^2)≤Y^2*X^(-c) := by
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
    (edgePrimes X) (completionRelation X s P z second js) (Nat.floor X) (pairWeight X s)
    (pairLo X s second js) (pairHi X s z second js) (physicalCut X)
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
        obtain ⟨a,ha,he,hr⟩ := hr
        have hsource := source_in_collection X s P z second js hjs _ hr
        have hphysical := ((LongPairCollectionWork.mem_source X s P z _).mp hsource).2.2.2.2.2
        have hupper := LongPairLargeGeometryWork.large_source_upper X s hX hs hs1 hlog _ hsource
        rw [ShortPairSplitWork.index_rebuild,he,Nat.cast_mul] at hphysical hupper
        exact ⟨by simpa only [show (545/1000:ℝ)=109/200 by norm_num] using hphysical.le,
          (hB q hq).2.1.le,(Finset.mem_filter.mp hq).2,
          hupper.le.trans (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith))⟩)
    (fun a ha q hq hn => mask_zero X s P z second js hjs hX hs hg a ha q
      (Finset.mem_filter.mp hq).1 hn)
  change (1/X)*(∫ x in Icc X (2*X),
    (edgeMaskedSum X s second js (x-x*((X^(101/1000:ℝ)/2)/X)) x).re^2)≤_ at hb
  simp_rw [←kernel_eq_masked X s second js hjs hX hs hg] at hb
  exact hb

#print axioms eventually_edge_square
run_cmd do
  for decl in [``kernel_eq_masked, ``eventually_edge_square] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairEdgeProfileMeanWork
