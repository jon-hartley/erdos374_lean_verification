import LongPairSmallProfileMeanWork
import ProductCappedMasksWork

/-! Large-band long-pair profiles restricted to the proved flat product cap.
The complementary high strip is not estimated or discarded. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairLargeFlatProfileMeanWork
open LongPairProfilesWork ShortPairSplitWork LongerTupleActualProfiles
open LongPairSmallProfileMeanWork ProductCappedMasksWork
open SieveWeightedCutoffs SieveBoxedFamily SieveGeometricGrid
open ShortSingletonMasks ShortSingletonEndpoints UpperAfter545Remaining
open PositiveSharpBoxedCount
open LongerTupleProfile

def cappedKernel (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (U : ℝ) (f : ℕ → ℝ) : ℝ :=
  pairKernel X s P z second js (fun m => if (m:ℝ)≤U then f m else 0)

def cappedLo (X s U : ℝ) (second : Bool) (js : List ℕ) (a : PairRep) : ℕ :=
  min (pairLo X s second js a) (upperEndpoint U (ShortPairSplitWork.index a))
def cappedHi (X s U : ℝ) (z : ℝ → ℝ) (second : Bool) (js : List ℕ) (a : PairRep) : ℕ :=
  min (pairHi X s z second js a) (upperEndpoint U (ShortPairSplitWork.index a))

def cappedMaskedSum (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (U L R : ℝ) : ℂ :=
  LongerTupleMaskedCollection.maskedSum (pairSupport X s P z second js)
    ShortPairSplitWork.index (longPrimeSupport X) (pairWeight X s)
    (cappedLo X s U second js) (cappedHi X s U z second js) (physicalCut X) L R

theorem kernel_eq_masked (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length=2) (hX : 1<X)
    (hs : 0<s) (hg : BandGeometry X s P z) (U L R : ℝ) (hU : 0≤U) :
    (cappedKernel X s P z second js U (floorKernel L R):ℂ) =
      cappedMaskedSum X s P z second js U L R := by
  unfold cappedKernel
  rw [pairKernel_eq_source,completion_sum second (pairSource X s P z second js) (longPrimeSupport X)
    (pairSource_length X s P z second js hjs)
    (pairSource_prime_mem X s P z second js hjs hX.le hs hg)]
  unfold cappedMaskedSum cappedLo cappedHi
  rw [maskedSum_cap _ _ _ _ _ _ _ U L R hU
    (fun a ha => pairSupport_index_pos X s P z second js hjs (by linarith) a ha)]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro q hq
  have hcomp := LongPairProfilesWork.completion_iff X s P z second js hjs
    (by linarith) hs hg a ha q hq
  have hp : a.1∈P := by
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp ha
    rw [←he]
    exact ((mem_source X s P z true js r).mp (Finset.mem_filter.mp hr).1).1
  have hgeom := hg a.1 hp
  have he := box_pool_high_prefix X (level X s/a.1) s (z a.1) (selectedIndex second js)
    (ShortPairSplitWork.index a) q (by linarith) (by linarith [hgeom.2.2.1])
    (pairSupport_cutoff_pos X s P z second js hjs hs hg a ha)
    (pairSupport_index_pos X s P z second js hjs (by linarith) a ha)
  simp only [hcomp,ShortPairSplitWork.index_rebuild]
  simp only [pairHi,pairLo]
  rw [←he]
  by_cases hc : InBox (level X s/a.1) s (q:ℝ) (selectedIndex second js) ∧ (q:ℝ)<z a.1 ∧
      X^(109/200:ℝ)<((ShortPairSplitWork.index a*q:ℕ):ℝ) <;>
    by_cases hu : ((ShortPairSplitWork.index a*q:ℕ):ℝ)≤U <;>
      simp only [hc,hu,ite_true,ite_false,originalWeight,pairWeight,rebuild,
        and_true,Complex.ofReal_zero,mul_zero,zero_mul,mul_one]

def cappedRelation (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (U : ℝ) (m q : ℕ) : Prop :=
  completionRelation X s P z second js m q ∧ ((m*q:ℕ):ℝ)≤U

theorem capped_mask_zero (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length=2) (hX : 1<X)
    (hs : 0<s) (hg : BandGeometry X s P z) (U : ℝ) (hU : 0≤U)
    (a : PairRep) (ha : a∈pairSupport X s P z second js)
    (q : ℕ) (hq : q∈longPrimeSupport X)
    (hn : ¬cappedRelation X s P z second js U (ShortPairSplitWork.index a) q) :
    (prefixIndicator (cappedHi X s U z second js a) q-
      prefixIndicator (cappedLo X s U second js a) q)*
        (1-prefixIndicator (physicalCut X (ShortPairSplitWork.index a)) q)=0 := by
  unfold cappedHi cappedLo
  rw [cap_mask U _ _ _ _ q hU
    (pairSupport_index_pos X s P z second js hjs (by linarith) a ha)]
  by_cases hu : ((ShortPairSplitWork.index a*q:ℕ):ℝ)≤U
  · simp only [hu,ite_true]
    exact mask_zero X s P z second js hjs hX hs hg a ha q hq (fun hr => hn ⟨hr,hu⟩)
  · simp only [hu,ite_false]

theorem large_support_lower (X s : ℝ) (second : Bool) (js : List ℕ)
    (hX : 1<X) (a : PairRep)
    (ha : a∈pairSupport X s (largePrimes X) (cutoffThree X s) second js) :
    X^(47/100:ℝ)≤(ShortPairSplitWork.index a:ℝ) := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hp,hd,_,_,_⟩ := (mem_source X s _ _ true js r).mp (Finset.mem_filter.mp hr).1
  have hpband := PositiveSharpSieveDecomposition.large_band_bounds X r.1 hp
  have hd1 : (1:ℝ)≤r.2.1 := by
    exact_mod_cast UpperAfter545Geometry.smallCarrier_pos _ _ _ hd
  have hp0 : (0:ℝ)≤r.1 := by positivity
  have hpd : X^(9/35:ℝ)≤((r.1*r.2.1:ℕ):ℝ) := by
    rw [Nat.cast_mul]
    exact hpband.2.1.trans (by nlinarith)
  have hother := (Finset.mem_filter.mp hr).2.2
  have hh := mul_le_mul hpd hother.le (by positivity)
    (by positivity : 0≤((r.1*r.2.1:ℕ):ℝ))
  rw [←Real.rpow_add (by linarith : 0<X)] at hh
  apply (Real.rpow_le_rpow_of_exponent_le hX.le
    (by norm_num : (47/100:ℝ)≤9/35+8/35)).trans
  simpa only [ShortPairSplitWork.index,drop,Nat.cast_mul] using hh

theorem eventually_capped_square (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ (second : Bool) (js : List ℕ), js.length=2 →
        let Y : ℝ := X^(101/1000:ℝ)/2
        (1/X)*(∫ x in Icc X (2*X), cappedKernel X s (largePrimes X)
          (cutoffThree X s) second js (X^(26/35:ℝ))
          (floorKernel (x-x*(Y/X)) x)^2)≤Y^2*X^(-c) := by
  obtain ⟨c,hc,hmean⟩ := LongPairFlatGlobalMeanWork.eventually_bound (α:=PairRep) 3
  refine ⟨c,hc,?_⟩
  filter_upwards [hmean,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1000)] with X hm hX hlog
  refine ⟨hX,hlog,?_⟩
  intro second js hjs
  dsimp only
  let P := largePrimes X
  let z := cutoffThree X s
  let U := X^(26/35:ℝ)
  have hU : 0≤U := by dsimp [U]; positivity
  have hg : BandGeometry X s P z := large_band_geometry X s hX hs hs1 hlog
  have hB (q : ℕ) (hq : q∈longPrimeSupport X) := (mem_longPrimeSupport X q (by linarith)).mp hq
  have hb := hm.2 (pairSupport X s P z second js) ShortPairSplitWork.index ShortPairSplitWork.encode
    (longPrimeSupport X) (cappedRelation X s P z second js U) (Nat.floor X) (pairWeight X s)
    (cappedLo X s U second js) (cappedHi X s U z second js) (physicalCut X)
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
        obtain ⟨⟨a,ha,he,_⟩,hu⟩ := hr
        exact ⟨by simpa only [he] using large_support_lower X s second js hX a ha,
          (hB q hq).2.1.le,by simpa only [Nat.cast_mul] using hu⟩)
    (fun a ha q hq hn => capped_mask_zero X s P z second js hjs hX hs hg U hU a ha q hq hn)
  have heq : (fun x : ℝ => cappedKernel X s P z second js U
      (floorKernel (x-x*((X^(101/1000:ℝ)/2)/X)) x)^2) =
      (fun x => (cappedMaskedSum X s P z second js U
        (x-x*((X^(101/1000:ℝ)/2)/X)) x).re^2) := by
    funext x
    have he := congrArg Complex.re (kernel_eq_masked X s P z second js hjs hX hs hg U
      (x-x*((X^(101/1000:ℝ)/2)/X)) x hU)
    simpa only [Complex.ofReal_re] using congrArg (fun r:ℝ => r^2) he
  change (1/X)*(∫ x in Icc X (2*X), cappedKernel X s P z second js U
    (floorKernel (x-x*((X^(101/1000:ℝ)/2)/X)) x)^2)≤_
  rw [heq]
  exact hb

#print axioms eventually_capped_square
run_cmd do
  for decl in [``kernel_eq_masked, ``capped_mask_zero, ``large_support_lower,
      ``eventually_capped_square] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairLargeFlatProfileMeanWork
