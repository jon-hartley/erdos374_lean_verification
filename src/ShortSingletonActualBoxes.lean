import ShortSingletonEndpoints
import ShortSingletonMaskedCollection

/-! Exact accepted-box partition of the actual surviving signed singleton
sector. Global prime support, p-dependent box endpoints, false small weights,
the physical pdq high mask and all pd collisions are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ShortSingletonActualBoxes
open ShortSingletonSector ShortSingletonBoxes ShortSingletonEndpoints
open SieveWeightedCutoffs SieveUpperBoxing PositiveSharpBoxedCount SieveGeometricGrid
open UpperAfter545Sectors UpperAfter545Remaining ShortSingletonCollection
open ShortSingletonMasks ShortSingletonMaskedCollection ShortSingletonComplex

def primeCutoff (X : ℝ) : ℕ := Nat.floor (X^(8/35:ℝ))
def shortPrimes (X : ℝ) : Finset ℕ :=
  (Finset.range (primeCutoff X+1)).filter (fun q => q.Prime ∧ X^(1/25:ℝ) < (q:ℝ))

def boxKernel (X s : ℝ) (j : ℕ) (f : ℕ → ℝ) : ℝ :=
  -(∑ p ∈ largePrimes X, ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
    ∑ q ∈ shortPrimes X,
      SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) false d *
        (if InBox (level X s/p) s (q:ℝ) j then highKernel X f (p*d*q) else 0))

def pairSupport (X s : ℝ) : Finset (ℕ × ℕ) :=
  representations (largePrimes X) (fun p => SieveUpperBoxWindow.smallCarrier (level X s/p) s)

def pairWeight (X s : ℝ) (a : ℕ × ℕ) : ℂ :=
  (SieveSmallWeights.weight ((level X s/a.1)^s) ((level X s/a.1)^(s^2)) false a.2 : ℝ)

def lowerEndpoint (X s : ℝ) (j p : ℕ) : ℕ := gridLo (level X s/p) s j
def upperEndpoint (X s : ℝ) (j p : ℕ) : ℕ := gridHi (level X s/p) s j

def boxMaskedSum (X s : ℝ) (j : ℕ) (L R : ℝ) : ℂ :=
  maskedSum (pairSupport X s) (shortPrimes X) (pairWeight X s)
    (lowerEndpoint X s j) (upperEndpoint X s j) (physicalCut X) L R

theorem mem_shortPrimes (X : ℝ) (q : ℕ) (hX : 0 ≤ X) :
    q ∈ shortPrimes X ↔ q.Prime ∧ X^(1/25:ℝ) < (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ) := by
  simp only [shortPrimes, primeCutoff, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
    Nat.le_floor_iff (Real.rpow_nonneg hX _)]
  tauto

theorem shortPrimes_le_cutoff (X : ℝ) (q : ℕ) (hq : q ∈ shortPrimes X) :
    q ≤ primeCutoff X := by
  exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hq).1)

theorem surviving_subset_shortPrimes (X D s : ℝ) (hX : 0 ≤ X) (hD : 1 < D) (hs : 0 < s) :
    survivingPrimes X D s (D^(1/3:ℝ)) ⊆ shortPrimes X := by
  intro q hq
  have hh := (mem_survivingPrimes_iff_boxes X D s q hD hs).mp hq
  exact (mem_shortPrimes X q hX).mpr ⟨hh.1,hh.2.1,hh.2.2.1⟩

theorem box_indicator_sum (X D s : ℝ) (q : ℕ) (v : ℝ)
    (hX : 0 ≤ X) (hD : 1 < D) (hs : 0 < s) (hq : q ∈ shortPrimes X) :
    (∑ j ∈ acceptedIndices s, if InBox D s (q:ℝ) j then v else 0) =
      if q ∈ survivingPrimes X D s (D^(1/3:ℝ)) then v else 0 := by
  have hqp := (mem_shortPrimes X q hX).mp hq
  by_cases hm : q ∈ survivingPrimes X D s (D^(1/3:ℝ))
  · rw [ite_eq_left hm]
    obtain ⟨j,hj,hb⟩ := ((mem_survivingPrimes_iff_boxes X D s q hD hs).mp hm).2.2.2
    rw [Finset.sum_eq_single j]
    · exact ite_eq_left hb
    · intro k hk hkj
      have hnb : ¬InBox D s (q:ℝ) k := fun hbk =>
        hkj (box_unique D s q hD hs k j hbk hb)
      exact ite_eq_right hnb
    · intro hjnot
      exact False.elim (hjnot hj)
  · rw [ite_eq_right hm]
    apply Finset.sum_eq_zero
    intro j hj
    have hnb : ¬InBox D s (q:ℝ) j := fun hb => hm
      ((mem_survivingPrimes_iff_boxes X D s q hD hs).mpr
        ⟨hqp.1,hqp.2.1,hqp.2.2,j,hj,hb⟩)
    exact ite_eq_right hnb

theorem prime_box_sum (X D s : ℝ) (f : ℕ → ℝ)
    (hX : 0 ≤ X) (hD : 1 < D) (hs : 0 < s) :
    (∑ q ∈ survivingPrimes X D s (D^(1/3:ℝ)), f q) =
      ∑ j ∈ acceptedIndices s, ∑ q ∈ shortPrimes X, if InBox D s (q:ℝ) j then f q else 0 := by
  calc
    _ = ∑ q ∈ survivingPrimes X D s (D^(1/3:ℝ)),
        if q ∈ survivingPrimes X D s (D^(1/3:ℝ)) then f q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (ite_eq_left hq).symm
    _ = ∑ q ∈ shortPrimes X,
        if q ∈ survivingPrimes X D s (D^(1/3:ℝ)) then f q else 0 :=
      Finset.sum_subset (surviving_subset_shortPrimes X D s hX hD hs)
        (by intro q _ hn; exact ite_eq_right hn)
    _ = ∑ q ∈ shortPrimes X, ∑ j ∈ acceptedIndices s,
        if InBox D s (q:ℝ) j then f q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (box_indicator_sum X D s q (f q) hX hD hs hq).symm
    _ = _ := Finset.sum_comm

theorem surviving_eq_box_sum (X s : ℝ) (f : ℕ → ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    survivingSingletonKernel X s f = ∑ j ∈ acceptedIndices s, boxKernel X s j f := by
  unfold survivingSingletonKernel boxKernel
  rw [Finset.sum_neg_distrib]
  congr 1
  calc
    _ = ∑ p ∈ largePrimes X, ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
        ∑ j ∈ acceptedIndices s, ∑ q ∈ shortPrimes X,
          if InBox (level X s/p) s (q:ℝ) j then
            SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) false d *
              highKernel X f (p*d*q) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hg := UpperAfter545Geometry.large_geometry X s p hX hs hs1 hlog hp
      apply Finset.sum_congr rfl
      intro d _
      exact prime_box_sum X (level X s/p) s _ (by linarith) hg.2.2.1 hs
    _ = ∑ p ∈ largePrimes X, ∑ j ∈ acceptedIndices s,
        ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s, ∑ q ∈ shortPrimes X,
          if InBox (level X s/p) s (q:ℝ) j then
            SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) false d *
              highKernel X f (p*d*q) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ = _ := by
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_comm]

theorem boxKernel_eq_masked (X s : ℝ) (j : ℕ) (L R : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    (boxKernel X s j (floorKernel L R):ℂ) = -boxMaskedSum X s j L R := by
  unfold boxKernel boxMaskedSum pairSupport
  rw [dependent_maskedSum]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hg := UpperAfter545Geometry.large_geometry X s p hX hs hs1 hlog hp
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos := (ShortSingletonGeometry.actual_small_divisor_bound X s p d hX hs hs1 hlog hp hd).1
  apply Finset.sum_congr rfl
  intro q _
  rw [boxed_highKernel X (level X s/p) s j (p*d) q _ (by linarith) hg.2.2.1 hs
    (Nat.mul_pos hg.1 hdpos)]
  unfold pairWeight lowerEndpoint upperEndpoint
  ring

theorem singleton_floor_eq_masked (X s L R : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    (singletonRemainder X s L R:ℂ) = -(∑ j ∈ acceptedIndices s, boxMaskedSum X s j L R) := by
  unfold singletonRemainder
  rw [singletonKernel_eq_surviving X s _ hX hs hs1 hlog,
    surviving_eq_box_sum X s _ hX hs hs1 hlog]
  push_cast
  simp_rw [boxKernel_eq_masked X s _ L R hX hs hs1 hlog]
  simp only [Finset.sum_neg_distrib]

theorem singleton_floor_eq_modes (X s L R : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    (singletonRemainder X s L R:ℂ) =
      -(∑ j ∈ acceptedIndices s, ∑ t : Mode (primeCutoff X), scalar (primeCutoff X) t *
        productSum (support (pairSupport X s)) (shortPrimes X)
          (modeCoefficient (pairSupport X s) (primeCutoff X) t (pairWeight X s)
            (lowerEndpoint X s j) (upperEndpoint X s j) (physicalCut X))
          (rightPhase (primeCutoff X) t) L R) := by
  rw [singleton_floor_eq_masked X s L R hX hs hs1 hlog]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact maskedSum_expansion (pairSupport X s) (shortPrimes X) (primeCutoff X) (pairWeight X s)
    (lowerEndpoint X s j) (upperEndpoint X s j) (physicalCut X) L R
    (fun q hq => shortPrimes_le_cutoff X q hq)

run_cmd do
  for decl in [``mem_shortPrimes, ``shortPrimes_le_cutoff, ``surviving_subset_shortPrimes,
      ``box_indicator_sum, ``prime_box_sum, ``surviving_eq_box_sum, ``boxKernel_eq_masked,
      ``singleton_floor_eq_masked, ``singleton_floor_eq_modes] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL SIGNED SINGLETON BOX PARTITION AND COLLECTED FOURIER IDENTITY PASSED"

end ShortSingletonActualBoxes
