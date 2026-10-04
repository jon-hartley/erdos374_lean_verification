import ShortSingletonGeometry
import ShortSingletonBoxes
import UpperAfter545Remaining

/-! Exact signed large-band singleton/rest partition. The original false
small weights, inner minus sign, physical high mask and all collisions stay
literal. Reindexing and deletion of zero high kernels assert no mean bound. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ShortSingletonSector
open SieveWeightedCutoffs SieveUpperBoxing PositiveSharpBoxedCount
open UpperAfter545Sectors UpperAfter545Remaining

def singletonTuples (X D s z : ℝ) : Finset (List ℕ) :=
  (innerFamily D s z).filter (fun t => isSingleton t ∧ ¬noShortSingleton X t)

def singletonPrimes (X D s z : ℝ) : Finset ℕ :=
  (SieveBoxedFamily.pool D s z).filter
    (fun q => [q] ∈ innerFamily D s z ∧ (q:ℝ) ≤ X^(8/35:ℝ))

def survivingPrimes (X D s z : ℝ) : Finset ℕ :=
  (singletonPrimes X D s z).filter (fun q => X^(1/25:ℝ) < (q:ℝ))

def singletonTupleKernel (X s : ℝ) (f : ℕ → ℝ) : ℝ :=
  -(∑ p ∈ largePrimes X, ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
    ∑ t ∈ singletonTuples X (level X s/p) s (cutoffThree X s p),
      SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) false d *
        highKernel X f (p*(d*t.prod)))

def singletonKernel (X s : ℝ) (f : ℕ → ℝ) : ℝ :=
  -(∑ p ∈ largePrimes X, ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
    ∑ q ∈ singletonPrimes X (level X s/p) s (cutoffThree X s p),
      SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) false d *
        highKernel X f (p*d*q))

def survivingSingletonKernel (X s : ℝ) (f : ℕ → ℝ) : ℝ :=
  -(∑ p ∈ largePrimes X, ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
    ∑ q ∈ survivingPrimes X (level X s/p) s (cutoffThree X s p),
      SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) false d *
        highKernel X f (p*d*q))

def largeRestKernel (X s : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ p ∈ largePrimes X,
    ((∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
      ∑ t ∈ (outerFamily (level X s/p) s (cutoffThree X s p)).filter (fun t => t ≠ []),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) true d *
          highKernel X f (p*(d*t.prod))) -
    ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
      ∑ t ∈ (innerFamily (level X s/p) s (cutoffThree X s p)).filter (fun t => ¬isSingleton t),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) false d *
          highKernel X f (p*(d*t.prod)))

def singletonRemainder (X s L R : ℝ) : ℝ := singletonKernel X s (floorKernel L R)

def restRemainder (X s L R : ℝ) : ℝ :=
  largeRestKernel X s (floorKernel L R) + smallRemainingRemainder X s L R

theorem noShortSingleton_singleton (X : ℝ) (q : ℕ) :
    noShortSingleton X [q] ↔ X^(8/35:ℝ) < (q:ℝ) := by
  simp [noShortSingleton]

theorem singletonTuples_eq_image (X D s z : ℝ) (hD : 1 < D) (hs : 0 < s) :
    singletonTuples X D s z = (singletonPrimes X D s z).image (fun q => [q]) := by
  ext t
  constructor
  · intro ht
    obtain ⟨ht,⟨hsingle,hnot⟩⟩ := Finset.mem_filter.mp ht
    obtain ⟨q,rfl⟩ := hsingle
    have hp := ((mem_innerFamily D s z hD hs [q]).mp ht).1 q (by simp)
    have hq : (q:ℝ) ≤ X^(8/35:ℝ) :=
      le_of_not_gt (fun h => hnot ((noShortSingleton_singleton X q).mpr h))
    exact Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hp,ht,hq⟩,rfl⟩
  · intro ht
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨_,ht,hshort⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨ht,⟨q,rfl⟩,
      fun h => (not_lt_of_ge hshort) ((noShortSingleton_singleton X q).mp h)⟩

theorem singleton_tuple_sum (X D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (f : List ℕ → ℝ) :
    (∑ t ∈ singletonTuples X D s z, f t) = ∑ q ∈ singletonPrimes X D s z, f [q] := by
  rw [singletonTuples_eq_image X D s z hD hs]
  exact Finset.sum_image (fun q _ r _ h => by simpa using h)

theorem inner_filter_split (X D s z : ℝ) (f : List ℕ → ℝ) :
    (∑ t ∈ (innerFamily D s z).filter (fun t => ¬noShortSingleton X t), f t) =
      (∑ t ∈ singletonTuples X D s z, f t) +
        ∑ t ∈ (innerFamily D s z).filter (fun t => ¬isSingleton t), f t := by
  simp only [singletonTuples, Finset.sum_filter]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hs : isSingleton t
  · by_cases hn : noShortSingleton X t <;> simp [hs,hn]
  · have hn : ¬noShortSingleton X t := by
      rintro ⟨q,hq,_⟩
      exact hs ⟨q,hq⟩
    simp [hs,hn]

theorem large_tuple_partition (X s : ℝ) (f : ℕ → ℝ) :
    remainingKernel X s (largePrimes X) (cutoffThree X s) f =
      singletonTupleKernel X s f + largeRestKernel X s f := by
  unfold remainingKernel singletonTupleKernel largeRestKernel
  simp_rw [inner_filter_split]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem singletonTupleKernel_eq (X s : ℝ) (f : ℕ → ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    singletonTupleKernel X s f = singletonKernel X s f := by
  unfold singletonTupleKernel singletonKernel
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hg := UpperAfter545Geometry.large_geometry X s p hX hs hs1 hlog hp
  apply Finset.sum_congr rfl
  intro d _
  rw [singleton_tuple_sum X _ s _ hg.2.2.1 hs]
  simp only [List.prod_cons, List.prod_nil, mul_one, Nat.mul_assoc]

theorem large_partition (X s : ℝ) (f : ℕ → ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    remainingKernel X s (largePrimes X) (cutoffThree X s) f =
      singletonKernel X s f + largeRestKernel X s f := by
  rw [large_tuple_partition, singletonTupleKernel_eq X s f hX hs hs1 hlog]

/-- The small remaining band stays literally unchanged in restRemainder. -/
theorem upperRemaining_partition (X s L R : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    upperRemainingRemainder X s L R = singletonRemainder X s L R + restRemainder X s L R := by
  unfold upperRemainingRemainder largeRemainingRemainder singletonRemainder restRemainder
  rw [large_partition X s _ hX hs hs1 hlog]
  ring

theorem complete_high_partition (X s x y : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    MomentSmallRemainder.high X s (109/200) x y =
      lowerHighRemainder X s (x-y) x + singletonRemainder X s (x-y) x + restRemainder X s (x-y) x := by
  rw [complete_high_eq_lower_add_upper X s x y hX hs hs1 hlog,
    upperRemaining_partition X s (x-y) x hX hs hs1 hlog]
  ring

theorem singletonKernel_eq_surviving (X s : ℝ) (f : ℕ → ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    singletonKernel X s f = survivingSingletonKernel X s f := by
  unfold singletonKernel survivingSingletonKernel survivingPrimes
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : X^(1/25:ℝ) < (q:ℝ)
  · simp only [hq, ite_true]
  · have hh : ¬X^(109/200:ℝ) < ((p*d*q:ℕ):ℝ) := fun hh =>
      hq (ShortSingletonGeometry.high_implies_short_lower X s p d q hX hs hs1 hlog hp hd hh)
    simp only [hq, ite_false, highKernel, ite_eq_right hh, mul_zero]

theorem mem_singletonPrimes_iff_boxes (X D s : ℝ) (q : ℕ) (hD : 1 < D) (hs : 0 < s) :
    q ∈ singletonPrimes X D s (D^(1/3:ℝ)) ↔
      q.Prime ∧ (q:ℝ) ≤ X^(8/35:ℝ) ∧
        ∃ j ∈ ShortSingletonBoxes.acceptedIndices s, SieveGeometricGrid.InBox D s (q:ℝ) j := by
  constructor
  · intro hq
    obtain ⟨_,ht,hshort⟩ := Finset.mem_filter.mp hq
    have hb := (ShortSingletonBoxes.inner_singleton_iff D s q hD hs).mp ht
    exact ⟨hb.1,hshort,hb.2⟩
  · rintro ⟨hq,hshort,hb⟩
    have ht := (ShortSingletonBoxes.inner_singleton_iff D s q hD hs).mpr ⟨hq,hb⟩
    have hp := ((mem_innerFamily D s _ hD hs [q]).mp ht).1 q (by simp)
    exact Finset.mem_filter.mpr ⟨hp,ht,hshort⟩

theorem mem_survivingPrimes_iff_boxes (X D s : ℝ) (q : ℕ) (hD : 1 < D) (hs : 0 < s) :
    q ∈ survivingPrimes X D s (D^(1/3:ℝ)) ↔
      q.Prime ∧ X^(1/25:ℝ) < (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ) ∧
        ∃ j ∈ ShortSingletonBoxes.acceptedIndices s, SieveGeometricGrid.InBox D s (q:ℝ) j := by
  simp only [survivingPrimes, Finset.mem_filter, mem_singletonPrimes_iff_boxes X D s q hD hs]
  tauto

run_cmd do
  for decl in [``noShortSingleton_singleton, ``singletonTuples_eq_image,
      ``singleton_tuple_sum, ``inner_filter_split, ``large_tuple_partition,
      ``singletonTupleKernel_eq, ``large_partition, ``upperRemaining_partition,
      ``complete_high_partition, ``singletonKernel_eq_surviving,
      ``mem_singletonPrimes_iff_boxes, ``mem_survivingPrimes_iff_boxes] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT SIGNED LARGE SINGLETON PARTITION AND SURVIVING PRIME REINDEXING PASSED"

end ShortSingletonSector
