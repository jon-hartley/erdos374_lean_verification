import LongPairProfilesWork
import LongPairFlatGlobalMeanWork

/-! Literal small-band long-pair profile second means, with actual-completion activity. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairSmallProfileMeanWork
open LongPairProfilesWork ShortPairSplitWork LongerTupleActualProfiles
open LongerTupleEncoding (Representation)
open LongerTupleProfile SieveWeightedCutoffs SieveBoxedFamily SieveGeometricGrid
open ShortSingletonMasks ShortSingletonEndpoints UpperAfter545Remaining

def completionRelation (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (m q : ℕ) : Prop :=
  ∃ a ∈ pairSupport X s P z second js,
    ShortPairSplitWork.index a=m ∧ rebuild second a q ∈ pairSource X s P z second js

theorem source_physical (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length=2) (hX : 1<X)
    (hs : 0<s) (hs1 : s≤1/1000) (hg : BandGeometry X s P z) (r : Representation)
    (hr : r∈pairSource X s P z second js) :
    (LongerTupleEncoding.index r:ℝ)<X^(1-3*s/2) := by
  obtain ⟨hp,hd,ht,_,_⟩ := (mem_source X s P z true js r).mp (Finset.mem_filter.mp hr).1
  have hlen := pairSource_length X s P z second js hjs r hr
  exact LongerTupleGeometry.physical_product_lt X s (z r.1) r.1 r.2.1 r.2.2 hX hs hs1
    (by have hh := (hg r.1 hp).1; omega) (hg r.1 hp).2.2.1 (hg r.1 hp).2.2.2 hd
    (by intro he; simp only [he,List.length_nil] at hlen; omega)
    (family_mem_or true _ s _ r.2.2 ht)

theorem support_bounds (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length=2) (hX : 1<X)
    (hs : 0<s) (hs1 : s≤1/1000) (hg : BandGeometry X s P z) (a : PairRep)
    (ha : a∈pairSupport X s P z second js) :
    2≤ShortPairSplitWork.index a ∧ (ShortPairSplitWork.index a:ℝ)≤X := by
  have hpos := pairSupport_index_pos X s P z second js hjs (by linarith) a ha
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  have hp := (mem_source X s P z true js r).mp (Finset.mem_filter.mp hr).1 |>.1
  have hdiv : r.1 ∣ ShortPairSplitWork.index (drop second r) := by
    simpa only [ShortPairSplitWork.index,drop,Nat.mul_assoc] using
      dvd_mul_right r.1 (r.2.1 * r.2.2.getD (if second then 0 else 1) 1)
  have hqp : 0<prime second r := by
    have hh := pairSource_prime_mem X s P z second js hjs (by linarith) hs hg r hr
    exact ((mem_longPrimeSupport X _ (by linarith)).mp hh).1.pos
  have hle : ShortPairSplitWork.index (drop second r)≤LongerTupleEncoding.index r := by
    rw [index_drop second r (pairSource_length X s P z second js hjs r hr)]
    exact Nat.le_mul_of_pos_right _ hqp
  refine ⟨(hg r.1 hp).1.trans (Nat.le_of_dvd hpos hdiv),?_⟩
  have htop : X^(1-3*s/2)≤X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX.le
      (show 1-3*s/2≤(1:ℝ) by linarith)
  exact (show (ShortPairSplitWork.index (drop second r):ℝ)≤(LongerTupleEncoding.index r:ℝ)
    by exact_mod_cast hle).trans ((source_physical X s P z second js hjs hX hs hs1 hg r hr).le.trans htop)

theorem mask_zero (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length=2) (hX : 1<X)
    (hs : 0<s) (hg : BandGeometry X s P z) (a : PairRep)
    (ha : a∈pairSupport X s P z second js) (q : ℕ) (hq : q∈longPrimeSupport X)
    (hn : ¬completionRelation X s P z second js (ShortPairSplitWork.index a) q) :
    (prefixIndicator (pairHi X s z second js a) q-prefixIndicator (pairLo X s second js a) q)*
      (1-prefixIndicator (physicalCut X (ShortPairSplitWork.index a)) q)=0 := by
  have hc := LongPairProfilesWork.completion_iff X s P z second js hjs (by linarith) hs hg a ha q hq
  have hp : a.1∈P := by
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp ha
    rw [←he]
    exact ((mem_source X s P z true js r).mp (Finset.mem_filter.mp hr).1).1
  have hgeom := hg a.1 hp
  have he := box_pool_high_prefix X (level X s/a.1) s (z a.1) (selectedIndex second js)
    (ShortPairSplitWork.index a) q (by linarith) (by linarith [hgeom.2.2.1])
    (pairSupport_cutoff_pos X s P z second js hjs hs hg a ha)
    (pairSupport_index_pos X s P z second js hjs (by linarith) a ha)
  have hncond := fun hb => hn ⟨a,ha,rfl,hc.mpr hb⟩
  simpa only [pairHi,pairLo,ite_eq_right hncond] using he.symm


theorem chosen_iff_allLong (X : ℝ) (second : Bool) (r : Representation)
    (hlen : r.2.2.length=2) :
    chosen X second r ↔ LongerTupleSector.allLong X r.2.2 := by
  rcases r with ⟨p,d,t⟩
  obtain ⟨u,v,rfl⟩ := List.length_eq_two.mp hlen
  cases second <;> simp [chosen,prime,drop,LongerTupleSector.allLong,and_comm]

theorem source_in_collection (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length=2) (r : Representation)
    (hr : r∈pairSource X s P z second js) : r∈LongPairCollectionWork.source X s P z := by
  obtain ⟨hsource,hchosen⟩ := Finset.mem_filter.mp hr
  obtain ⟨hp,hd,ht,_,hh⟩ := (mem_source X s P z true js r).mp hsource
  have hlen := (source_length X s P z true js r hsource).trans hjs
  exact (LongPairCollectionWork.mem_source X s P z r).mpr
    ⟨hp,hd,ht,hlen,(chosen_iff_allLong X second r hlen).mp hchosen,hh⟩

theorem support_lower (X s : ℝ) (second : Bool) (js : List ℕ) (hjs : js.length=2)
    (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (a : PairRep) (ha : a∈pairSupport X s (PositiveSharpBoxedCount.smallPrimes X s)
      (SieveCappedUpperMainTerms.cappedFourth X s) second js) :
    X^(47/100:ℝ)≤(ShortPairSplitWork.index a:ℝ) := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  have hgeom := LongPairCollectionWork.source_small_geometry X s hX hs hs1 hlog r
    (source_in_collection X s _ _ second js hjs r hr)
  have hother := (Finset.mem_filter.mp hr).2.2
  have hp := mul_le_mul hgeom.2.2.1 hother.le (by positivity)
    (by positivity : 0≤((r.1*r.2.1:ℕ):ℝ))
  rw [←Real.rpow_add (by linarith : 0<X)] at hp
  apply (Real.rpow_le_rpow_of_exponent_le hX.le
    (by norm_num : (47/100:ℝ)≤246/1000+8/35)).trans
  simpa only [ShortPairSplitWork.index,drop,Nat.cast_mul] using hp

theorem relation_bounds (X s : ℝ) (second : Bool) (js : List ℕ) (hjs : js.length=2)
    (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (m q : ℕ) (hr : completionRelation X s (PositiveSharpBoxedCount.smallPrimes X s)
      (SieveCappedUpperMainTerms.cappedFourth X s) second js m q) :
    X^(47/100:ℝ)≤(m:ℝ) ∧ X^(8/35:ℝ)≤(q:ℝ) ∧
      (m:ℝ)*(q:ℝ)≤X^(26/35:ℝ) := by
  obtain ⟨a,ha,he,hc⟩ := hr
  have hlo := support_lower X s second js hjs hX hs hs1 hlog a ha
  have hq := (Finset.mem_filter.mp hc).2.1
  rw [prime_rebuild] at hq
  have hg := LongPairCollectionWork.source_small_geometry X s hX hs hs1 hlog
    (rebuild second a q) (source_in_collection X s _ _ second js hjs _ hc)
  have hprod : (LongerTupleEncoding.index (rebuild second a q):ℝ)≤X^(26/35:ℝ) :=
    hg.2.1.le.trans (Real.rpow_le_rpow_of_exponent_le hX.le
      (show (26/35:ℝ)-s≤26/35 by linarith))
  rw [ShortPairSplitWork.index_rebuild,he,Nat.cast_mul] at hprod
  exact ⟨by simpa only [he] using hlo,hq.le,hprod⟩

theorem eventually_pair_square (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ (second : Bool) (js : List ℕ), js.length=2 →
        let Y : ℝ := X^(101/1000:ℝ)/2
        (1/X)*(∫ x in Icc X (2*X), pairKernel X s (PositiveSharpBoxedCount.smallPrimes X s)
          (SieveCappedUpperMainTerms.cappedFourth X s) second js
          (floorKernel (x-x*(Y/X)) x)^2)≤Y^2*X^(-c) := by
  obtain ⟨c,hc,hmean⟩ := LongPairFlatGlobalMeanWork.eventually_bound (α:=PairRep) 3
  refine ⟨c,hc,?_⟩
  filter_upwards [hmean,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1000)] with X hm hX hlog
  refine ⟨hX,hlog,?_⟩
  intro second js hjs
  dsimp only
  let P := PositiveSharpBoxedCount.smallPrimes X s
  let z := SieveCappedUpperMainTerms.cappedFourth X s
  have hg : BandGeometry X s P z := small_band_geometry X s hX hs hs1 hlog
  have hB (q : ℕ) (hq : q∈longPrimeSupport X) :=
    (mem_longPrimeSupport X q (by linarith)).mp hq
  have hb := hm.2 (pairSupport X s P z second js) ShortPairSplitWork.index ShortPairSplitWork.encode
    (longPrimeSupport X) (completionRelation X s P z second js) (Nat.floor X) (pairWeight X s)
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
    (fun m _ q _ hr => relation_bounds X s second js hjs hX hs hs1 hlog m q hr)
    (fun a ha q hq hn => mask_zero X s P z second js hjs hX hs hg a ha q hq hn)
  have heq : (fun x : ℝ => pairKernel X s P z second js
      (floorKernel (x-x*((X^(101/1000:ℝ)/2)/X)) x)^2) =
      (fun x => (pairMaskedSum X s P z second js (x-x*((X^(101/1000:ℝ)/2)/X)) x).re^2) := by
    funext x
    have he := congrArg Complex.re (pairKernel_eq_masked X s P z second js hjs hX hs hg
      (x-x*((X^(101/1000:ℝ)/2)/X)) x)
    simpa only [Complex.ofReal_re] using congrArg (fun r:ℝ => r^2) he
  change (1/X)*(∫ x in Icc X (2*X), pairKernel X s P z second js
    (floorKernel (x-x*((X^(101/1000:ℝ)/2)/X)) x)^2) ≤ _
  rw [heq]
  exact hb

#print axioms eventually_pair_square
run_cmd do
  for decl in [``source_physical, ``support_bounds, ``mask_zero,
      ``chosen_iff_allLong, ``source_in_collection, ``support_lower,
      ``relation_bounds, ``eventually_pair_square] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairSmallProfileMeanWork
