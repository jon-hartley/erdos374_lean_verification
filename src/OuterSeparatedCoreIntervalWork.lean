import OuterPrimeIntervalRestrictionWork
import OuterPairSourceDecompositionWork
import LongPairSeparatedCoreWork

/-! Exact fixed-box decomposition and constant-weight outer-prime intervals
for the actual separated core, including every core source restriction. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped BigOperators

namespace OuterSeparatedCoreIntervalWork
open LongerTupleEncoding LongerTupleActualProfiles SieveWeightedCutoffs
open PositiveSharpBoxedCount LongPairCloseDistinctMeanWork
open OuterPairSourceIntervalWork OuterPairPrimeIntervalWork
open OuterPairSourceDecompositionWork

def coreRestrictions (X : ℝ) (d a b p : ℕ) : Prop :=
  X^(26/35:ℝ)<(index (p,d,[a,b]):ℝ) ∧
  X^(229/1000:ℝ)<(b:ℝ) ∧ X^(229/1000:ℝ)<(a:ℝ) ∧
  a≠b ∧ X^(9/50:ℝ)<(Nat.dist a b:ℝ)

def coreBoxSource (X s : ℝ) (d a b i j p : ℕ) : Prop :=
  fixedBoxSource X s (largePrimes X) (cutoffThree X s) d a b i j p ∧
    coreRestrictions X d a b p

theorem mem_separated_iff (X s : ℝ) (p d a b : ℕ) :
    (p,d,[a,b])∈separatedSource X s ↔
      (p,d,[a,b])∈LongPairCollectionWork.source X s (largePrimes X) (cutoffThree X s) ∧
        coreRestrictions X d a b p := by
  simp [separatedSource,LongPairRepeatedCoreMeanWork.distinctSource,
    LongPairTwoSidedCoreMeanWork.twoSidedCoreSource,
    LongPairHighCoreMeanWork.highCoreSource,LongPairHighStripWork.highSource,
    coreRestrictions,tupleGap,ShortPairSplitWork.prime,and_assoc]

theorem coreRestrictions_mono (X : ℝ) (d a b p q : ℕ) (hpq : p≤q)
    (hp : coreRestrictions X d a b p) : coreRestrictions X d a b q := by
  have hm : index (p,d,[a,b]) ≤ index (q,d,[a,b]) := by
    simpa [index,Nat.mul_assoc] using Nat.mul_le_mul_right (d*(a*b)) hpq
  have hmR : (index (p,d,[a,b]):ℝ) ≤ index (q,d,[a,b]) := by exact_mod_cast hm
  exact ⟨hp.1.trans_le hmR,hp.2⟩

theorem separated_weight_eq_box_sum (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (p d a b : ℕ) :
    (if (p,d,[a,b])∈separatedSource X s then
      originalWeight X s true (p,d,[a,b]) else 0) =
    ∑ ij∈boxPairs s, if coreBoxSource X s d a b ij.1 ij.2 p then
      originalWeight X s true (p,d,[a,b]) else 0 := by
  have hg := large_band_geometry X s hX hs hs1 hlog
  have hD : ∀p∈largePrimes X,1<level X s/p := fun p hp => (hg p hp).2.2.1
  have hz : ∀p∈largePrimes X,cutoffThree X s p≤level X s/p :=
    fun p hp => (hg p hp).2.2.2
  simp only [mem_separated_iff]
  by_cases hQ : coreRestrictions X d a b p
  · simpa only [coreBoxSource,hQ,and_true] using
      source_weight_eq_box_sum X s (largePrimes X) (cutoffThree X s) hD hz hs p d a b
  · simp [coreBoxSource,hQ]

theorem eventually_core_box_interval (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ d a b i j : ℕ, ∃ lo hi : ℕ, ∃ c : ℂ, ‖c‖≤1 ∧
        ∀ p∈largePrimes X,
          (if coreBoxSource X s d a b i j p then
            originalWeight X s true (p,d,[a,b]) else 0) =
          if lo≤p ∧ p≤hi then c else 0 := by
  filter_upwards [OuterPairActualIntervalWork.eventually_actual_prime_interval s hs hs1]
    with X hX
  refine ⟨hX.1,hX.2.1,?_⟩
  intro d a b i j
  let f := fun p => if p∈primeSlice X s (largePrimes X) (cutoffThree X s) d a b i j then
    originalWeight X s true (p,d,[a,b]) else 0
  have hcap : ∀p∈largePrimes X, ‖f p‖≤1 := by
    intro p _
    dsimp [f]
    split_ifs
    · exact originalWeight_norm_le X s true _
    · simp
  obtain ⟨lo,hi,c,hc,hh⟩ := OuterPrimeIntervalRestrictionWork.restrict_weighted_interval
    (largePrimes X) f (coreRestrictions X d a b)
    (fun p _ q _ _ _ hpq _ hp _ => coreRestrictions_mono X d a b p q hpq hp)
    hcap (hX.2.2 d a b i j)
  refine ⟨lo,hi,c,hc,?_⟩
  intro p hp
  have he := hh p hp
  by_cases hQ : coreRestrictions X d a b p <;>
    by_cases hB : fixedBoxSource X s (largePrimes X) (cutoffThree X s) d a b i j p <;>
    simpa [f,primeSlice,hp,coreBoxSource,hQ,hB] using he

run_cmd do
  for decl in [``mem_separated_iff, ``coreRestrictions_mono,
      ``separated_weight_eq_box_sum, ``eventually_core_box_interval] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSeparatedCoreIntervalWork
