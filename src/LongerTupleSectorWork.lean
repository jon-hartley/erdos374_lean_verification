import ShortSingletonSector

/-! Exact partition of the literal upper rest by tuple length and a short
prime. Original signs, false/true weights and repeated entries are retained.
This finite identity makes no assertion that a sector has a small mean. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongerTupleSector
open SieveWeightedCutoffs SieveUpperBoxing PositiveSharpBoxedCount
open UpperAfter545Sectors UpperAfter545Remaining ShortSingletonSector
open SieveCappedUpperMainTerms (cappedFourth)

def hasShort (X : ℝ) (t : List ℕ) : Prop :=
  ∃ q ∈ t, (q:ℝ) ≤ X^(8/35:ℝ)

def allLong (X : ℝ) (t : List ℕ) : Prop :=
  ∀ q ∈ t, X^(8/35:ℝ) < (q:ℝ)

theorem allLong_iff_not_hasShort (X : ℝ) (t : List ℕ) :
    allLong X t ↔ ¬hasShort X t := by
  simp [allLong, hasShort]

theorem outer_length_cases (D s z : ℝ) (t : List ℕ)
    (ht : t ∈ outerFamily D s z) (hne : t ≠ []) :
    t.length = 2 ∨ 4 ≤ t.length := by
  have he : Even t.length := (Finset.mem_filter.mp ht).2.1
  obtain ⟨k,hk⟩ := he
  have hp : 0 < t.length := List.length_pos_iff.mpr hne
  omega

theorem inner_length_ge_three (D s z : ℝ) (t : List ℕ)
    (ht : t ∈ innerFamily D s z) (hn : ¬isSingleton t) :
    3 ≤ t.length := by
  have he : ¬Even t.length := (Finset.mem_filter.mp ht).2.1
  have h0 : t.length ≠ 0 := fun h => he (by simp [h])
  have h2 : t.length ≠ 2 := fun h => he (by simp [h])
  have h1 : t.length ≠ 1 := by
    intro h
    obtain ⟨q,rfl⟩ := List.length_eq_one_iff.mp h
    exact hn ⟨q,rfl⟩
  omega

theorem outer_sum_split (D s z : ℝ) (f : List ℕ → ℝ) :
    (∑ t ∈ (outerFamily D s z).filter (fun t => t ≠ []), f t) =
      (∑ t ∈ (outerFamily D s z).filter (fun t => 4 ≤ t.length), f t) +
        ∑ t ∈ (outerFamily D s z).filter (fun t => t.length = 2), f t := by
  simp only [Finset.sum_filter]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hn : t = []
  · subst t; simp
  · obtain h2 | h4 := outer_length_cases D s z t ht hn
    · simp [hn,h2]
    · have h2 : t.length ≠ 2 := by omega
      simp [hn,h4,h2]

theorem inner_sum_eq_higher (D s z : ℝ) (f : List ℕ → ℝ) :
    (∑ t ∈ (innerFamily D s z).filter (fun t => ¬isSingleton t), f t) =
      ∑ t ∈ (innerFamily D s z).filter (fun t => 3 ≤ t.length), f t := by
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hn : isSingleton t
  · obtain ⟨q,rfl⟩ := hn
    have hq : isSingleton [q] := ⟨q,rfl⟩
    simp [hq]
  · simp [hn,inner_length_ge_three D s z t ht hn]

theorem pair_sum_split (X D s z : ℝ) (f : List ℕ → ℝ) :
    (∑ t ∈ (outerFamily D s z).filter (fun t => t.length = 2), f t) =
      (∑ t ∈ (outerFamily D s z).filter
        (fun t => t.length = 2 ∧ hasShort X t), f t) +
      ∑ t ∈ (outerFamily D s z).filter
        (fun t => t.length = 2 ∧ allLong X t), f t := by
  simp only [Finset.sum_filter, allLong_iff_not_hasShort]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h2 : t.length = 2 <;> by_cases hs : hasShort X t <;> simp [h2,hs]

/-- A disjoint choice, even if the two actual primes coincide. -/
theorem pair_short_choice (X : ℝ) (a b : ℕ) :
    hasShort X [a,b] ↔ (b:ℝ) ≤ X^(8/35:ℝ) ∨
      ((a:ℝ) ≤ X^(8/35:ℝ) ∧ X^(8/35:ℝ) < (b:ℝ)) := by
  simp only [hasShort, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨q,hq,hshort⟩
    by_cases hb : (b:ℝ) ≤ X^(8/35:ℝ)
    · exact Or.inl hb
    · refine Or.inr ⟨?_,lt_of_not_ge hb⟩
      rcases hq with rfl | rfl
      · exact hshort
      · exact (hb hshort).elim
  · rintro (hb | ⟨ha,_⟩)
    · exact ⟨b,Or.inr rfl,hb⟩
    · exact ⟨a,Or.inl rfl,ha⟩

def selectedKernel (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (outer : Bool) (pick : List ℕ → Prop) (f : ℕ → ℝ) : ℝ :=
  ∑ p ∈ P, ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
    ∑ t ∈ ((if outer then outerFamily else innerFamily) (level X s/p) s (z p)).filter pick,
      SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) outer d *
        highKernel X f (p*(d*t.prod))

def restBand (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (f : ℕ → ℝ) : ℝ :=
  selectedKernel X s P z true (fun t => t ≠ []) f -
    selectedKernel X s P z false (fun t => ¬isSingleton t) f

def higherBand (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (f : ℕ → ℝ) : ℝ :=
  selectedKernel X s P z true (fun t => 4 ≤ t.length) f -
    selectedKernel X s P z false (fun t => 3 ≤ t.length) f

def shortPairBand (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (f : ℕ → ℝ) : ℝ :=
  selectedKernel X s P z true (fun t => t.length = 2 ∧ hasShort X t) f

def longPairBand (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (f : ℕ → ℝ) : ℝ :=
  selectedKernel X s P z true (fun t => t.length = 2 ∧ allLong X t) f

theorem band_partition (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (f : ℕ → ℝ) :
    restBand X s P z f = higherBand X s P z f +
      shortPairBand X s P z f + longPairBand X s P z f := by
  have ho (p d : ℕ) :
      (∑ t ∈ (outerFamily (level X s/p) s (z p)).filter (fun t => t ≠ []),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) true d *
          highKernel X f (p*(d*t.prod))) =
      (∑ t ∈ (outerFamily (level X s/p) s (z p)).filter (fun t => 4 ≤ t.length),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) true d *
          highKernel X f (p*(d*t.prod))) +
      (∑ t ∈ (outerFamily (level X s/p) s (z p)).filter (fun t => t.length = 2 ∧ hasShort X t),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) true d *
          highKernel X f (p*(d*t.prod))) +
      (∑ t ∈ (outerFamily (level X s/p) s (z p)).filter (fun t => t.length = 2 ∧ allLong X t),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) true d *
          highKernel X f (p*(d*t.prod))) := by
    rw [outer_sum_split, pair_sum_split]
    ring
  have hoK : selectedKernel X s P z true (fun t => t ≠ []) f =
      selectedKernel X s P z true (fun t => 4 ≤ t.length) f +
      selectedKernel X s P z true (fun t => t.length = 2 ∧ hasShort X t) f +
      selectedKernel X s P z true (fun t => t.length = 2 ∧ allLong X t) f := by
    unfold selectedKernel
    simp only [↓reduceIte, ←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro d _
    convert ho p d using 1 <;> congr!
  have hiK : selectedKernel X s P z false (fun t => ¬isSingleton t) f =
      selectedKernel X s P z false (fun t => 3 ≤ t.length) f := by
    unfold selectedKernel
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro d _
    convert inner_sum_eq_higher (level X s/p) s (z p)
      (fun t => SieveSmallWeights.weight ((level X s/p)^s)
        ((level X s/p)^(s^2)) false d * highKernel X f (p*(d*t.prod))) using 1 <;> congr!
  unfold restBand higherBand shortPairBand longPairBand
  rw [hoK, hiK]
  ring

def higherRemainder (X s L R : ℝ) : ℝ :=
  higherBand X s (largePrimes X) (cutoffThree X s) (floorKernel L R) +
    higherBand X s (smallPrimes X s) (cappedFourth X s) (floorKernel L R)

def shortPairRemainder (X s L R : ℝ) : ℝ :=
  shortPairBand X s (largePrimes X) (cutoffThree X s) (floorKernel L R) +
    shortPairBand X s (smallPrimes X s) (cappedFourth X s) (floorKernel L R)

def longPairRemainder (X s L R : ℝ) : ℝ :=
  longPairBand X s (largePrimes X) (cutoffThree X s) (floorKernel L R) +
    longPairBand X s (smallPrimes X s) (cappedFourth X s) (floorKernel L R)

theorem rest_partition (X s L R : ℝ) :
    restRemainder X s L R = higherRemainder X s L R +
      shortPairRemainder X s L R + longPairRemainder X s L R := by
  have hl : largeRestKernel X s (floorKernel L R) =
      restBand X s (largePrimes X) (cutoffThree X s) (floorKernel L R) := by
    simp only [largeRestKernel, restBand, selectedKernel, Bool.false_eq_true, ↓reduceIte,
      Finset.sum_sub_distrib]
    congr!
  have hs : smallRemainingKernel X s (floorKernel L R) =
      restBand X s (smallPrimes X s) (cappedFourth X s) (floorKernel L R) := by
    simp only [smallRemainingKernel, restBand, selectedKernel, Bool.false_eq_true, ↓reduceIte,
      Finset.sum_sub_distrib]
    congr!
  unfold restRemainder smallRemainingRemainder higherRemainder
    shortPairRemainder longPairRemainder
  rw [hl,hs,band_partition,band_partition]
  ring

/-- The literal negative rest is controlled by absolute higher/short-pair
errors and the signed negative part of the long-pair sector. -/
theorem rest_negative_part_le (X s L R : ℝ) :
    max (-restRemainder X s L R) 0 ≤
      |higherRemainder X s L R| + |shortPairRemainder X s L R| +
        max (-longPairRemainder X s L R) 0 := by
  rw [rest_partition]
  have hh := neg_le_abs (higherRemainder X s L R)
  have hs := neg_le_abs (shortPairRemainder X s L R)
  have hl := le_max_left (-longPairRemainder X s L R) (0 : ℝ)
  have hl0 := le_max_right (-longPairRemainder X s L R) (0 : ℝ)
  apply max_le
  · linarith
  · linarith [abs_nonneg (higherRemainder X s L R),
      abs_nonneg (shortPairRemainder X s L R)]

#print axioms rest_partition
#print axioms rest_negative_part_le

run_cmd do
  for decl in [``allLong_iff_not_hasShort, ``outer_length_cases,
      ``inner_length_ge_three, ``outer_sum_split, ``inner_sum_eq_higher,
      ``pair_sum_split, ``pair_short_choice, ``band_partition, ``rest_partition,
      ``rest_negative_part_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT LONGER TUPLE AND SHORT/LONG PAIR REST PARTITION PASSED"

end LongerTupleSector
