import UpperAfter545Geometry

/-! Exact disappearance of empty outer tuples and no-short inner singletons
above the physical .545 cutoff. Signed weights and all collisions remain. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace UpperAfter545Sectors
open SieveWeightedCutoffs SieveUpperBoxing PositiveSharpBoxedCount
open PositiveSharpRemainderAnalysisPhysical UpperAfter545Geometry
open SieveCappedUpperMainTerms (cappedFourth)

def noShortSingleton (X : ℝ) (t : List ℕ) : Prop :=
  ∃ q : ℕ, t = [q] ∧ X^(8/35:ℝ) < (q:ℝ)

def highKernel (X : ℝ) (f : ℕ → ℝ) (m : ℕ) : ℝ :=
  if X^(109/200:ℝ) < (m:ℝ) then f m else 0

def remainingKernel (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ p ∈ P,
    ((∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
      ∑ t ∈ (outerFamily (level X s/p) s (z p)).filter (fun t => t ≠ []),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) true d *
          highKernel X f (p*(d*t.prod))) -
    ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
      ∑ t ∈ (innerFamily (level X s/p) s (z p)).filter (fun t => ¬noShortSingleton X t),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) false d *
          highKernel X f (p*(d*t.prod)))

theorem highKernel_eq_zero (X : ℝ) (f : ℕ → ℝ) (m : ℕ)
    (hm : (m:ℝ) ≤ X^(109/200:ℝ)) : highKernel X f m = 0 := by
  simp only [highKernel, ite_eq_right (not_lt.mpr hm)]

theorem outer_high_filter (X s z : ℝ) (p d : ℕ) (f : ℕ → ℝ) (w : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : 0 < p) (hptop : (p:ℝ) ≤ Real.sqrt (2*X)) (hD : 1 < level X s/p)
    (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s) :
    (∑ t ∈ outerFamily (level X s/p) s z, w * highKernel X f (p*(d*t.prod))) =
      ∑ t ∈ (outerFamily (level X s/p) s z).filter (fun t => t ≠ []),
        w * highKernel X f (p*(d*t.prod)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : t = []
  · subst t
    have hm := physical_le_545 X (p*d*([].prod:ℕ)) hX.le
      (empty_physical_lt X s p d hX hs hs1 hlog hp hptop hD hd)
    have hz := highKernel_eq_zero X f _ hm
    simpa only [ne_eq, not_true_eq_false, ite_false, List.prod_nil, mul_one, mul_zero]
      using congrArg (fun v : ℝ => w*v) hz
  · simp only [ht, ne_eq, not_false_eq_true, ite_true]

theorem inner_high_filter (X s z : ℝ) (p d : ℕ) (f : ℕ → ℝ) (w : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hp : 0 < p)
    (hD : 1 < level X s/p) (hz : z ≤ level X s/p)
    (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s) :
    (∑ t ∈ innerFamily (level X s/p) s z, w * highKernel X f (p*(d*t.prod))) =
      ∑ t ∈ (innerFamily (level X s/p) s z).filter (fun t => ¬noShortSingleton X t),
        w * highKernel X f (p*(d*t.prod)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hsingle : noShortSingleton X t
  · obtain ⟨q,rfl,hq⟩ := hsingle
    have hm := physical_le_545 X (p*d*[q].prod) hX.le
      (inner_singleton_physical_lt X s z p d q hX hs hs1 hp hD hz hd ht hq.le)
    have he := highKernel_eq_zero X f _ hm
    have hs' : noShortSingleton X [q] := ⟨q,rfl,hq⟩
    simp only [hs', not_true_eq_false, ite_false, ←Nat.mul_assoc, he, mul_zero]
  · simp only [hsingle, not_false_eq_true, ite_true]

/-- Exact collection by physical index, with all original small weights and
tuple multiplicities. Only sectors proved physically low are removed. -/
theorem collected_high_eq_remaining (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (f : ℕ → ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hg : ∀ p ∈ P, 0 < p ∧ (p:ℝ) ≤ Real.sqrt (2*X) ∧
      1 < level X s/p ∧ z p ≤ level X s/p) :
    (∑ m ∈ upperSupport X s P z, upperCoefficient X s P z m * highKernel X f m) =
      remainingKernel X s P z f := by
  rw [upperSupport, upperCoefficient, FiniteDivisorFamily.sum_coefficient]
  simp_rw [inflated_kernel, SieveUpperBoxWindow.literal_kernel]
  unfold remainingKernel
  apply Finset.sum_congr rfl
  intro p hp
  have hgp := hg p hp
  congr 1
  · apply Finset.sum_congr rfl
    intro d hd
    exact outer_high_filter X s (z p) p d f _ hX hs hs1 hlog hgp.1 hgp.2.1 hgp.2.2.1 hd
  · apply Finset.sum_congr rfl
    intro d hd
    exact inner_high_filter X s (z p) p d f _ hX hs hs1 hgp.1 hgp.2.2.1 hgp.2.2.2 hd

theorem large_collected_high_eq_remaining (X s : ℝ) (f : ℕ → ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    (∑ m ∈ upperSupport X s (largePrimes X) (cutoffThree X s),
      upperCoefficient X s (largePrimes X) (cutoffThree X s) m * highKernel X f m) =
      remainingKernel X s (largePrimes X) (cutoffThree X s) f :=
  collected_high_eq_remaining X s _ _ f hX hs hs1 hlog
    (fun p hp => large_geometry X s p hX hs hs1 hlog hp)

theorem small_collected_high_eq_remaining (X s : ℝ) (f : ℕ → ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    (∑ m ∈ upperSupport X s (smallPrimes X s) (cappedFourth X s),
      upperCoefficient X s (smallPrimes X s) (cappedFourth X s) m * highKernel X f m) =
      remainingKernel X s (smallPrimes X s) (cappedFourth X s) f :=
  collected_high_eq_remaining X s _ _ f hX hs hs1 hlog
    (fun p hp => small_geometry X s p hX hs hs1 hlog hp)

theorem filtered_collected_eq_remaining (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (f : ℕ → ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hg : ∀ p ∈ P, 0 < p ∧ (p:ℝ) ≤ Real.sqrt (2*X) ∧
      1 < level X s/p ∧ z p ≤ level X s/p) :
    (∑ m ∈ (upperSupport X s P z).filter (fun m : ℕ => X^(109/200:ℝ) < (m:ℝ)),
      upperCoefficient X s P z m * f m) = remainingKernel X s P z f := by
  rw [←collected_high_eq_remaining X s P z f hX hs hs1 hlog hg, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  simp only [highKernel]
  split_ifs <;> simp

run_cmd do
  for decl in [``highKernel_eq_zero, ``outer_high_filter, ``inner_high_filter,
      ``collected_high_eq_remaining, ``large_collected_high_eq_remaining,
      ``small_collected_high_eq_remaining, ``filtered_collected_eq_remaining] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "UPPER PHYSICAL HIGH SECTOR ELIMINATION PASSED"

end UpperAfter545Sectors
