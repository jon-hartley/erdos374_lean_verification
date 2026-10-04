import UpperAfter545Sectors
import UpperAfter545SmallSingleton
import MomentSmallRemainder

/-! Exact complete-high reduction at .545.  The lower contribution retains
its negative coefficient. Every upper small weight and tuple collision stays
in the literal finite sums; no mean estimate is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace UpperAfter545Remaining
open SieveWeightedCutoffs SieveUpperBoxing PositiveSharpBoxedCount
open PositiveSharpRemainderAnalysisPhysical UpperAfter545Geometry UpperAfter545Sectors
open SieveCappedUpperMainTerms (cappedFourth)

def floorKernel (L R : ℝ) (m : ℕ) : ℝ :=
  (⌊R/m⌋₊:ℝ) - (⌊L/m⌋₊:ℝ) - (R-L)/m

def lowerHighRemainder (X s L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder
    ((SieveBoxedWindow.support (level X s) s (X^SieveWeightedScalarBudget.alpha s)).filter
      (fun m : ℕ => X^(109/200:ℝ) < (m:ℝ)))
    (fun m => -SieveBoxedWindow.coefficient (level X s) s
      (X^SieveWeightedScalarBudget.alpha s) m) L R

def isSingleton (t : List ℕ) : Prop := ∃ q : ℕ, t = [q]

def smallRemainingKernel (X s : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ p ∈ smallPrimes X s,
    ((∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
      ∑ t ∈ (outerFamily (level X s/p) s (cappedFourth X s p)).filter (fun t => t ≠ []),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) true d *
          highKernel X f (p*(d*t.prod))) -
    ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
      ∑ t ∈ (innerFamily (level X s/p) s (cappedFourth X s p)).filter
          (fun t => ¬isSingleton t),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) false d *
          highKernel X f (p*(d*t.prod)))

def largeRemainingRemainder (X s L R : ℝ) : ℝ :=
  remainingKernel X s (largePrimes X) (cutoffThree X s) (floorKernel L R)

def smallRemainingRemainder (X s L R : ℝ) : ℝ :=
  smallRemainingKernel X s (floorKernel L R)

def upperRemainingRemainder (X s L R : ℝ) : ℝ :=
  largeRemainingRemainder X s L R + smallRemainingRemainder X s L R

theorem filtered_remainder_kernel (X L R : ℝ) (S : Finset ℕ) (w : ℕ → ℝ) :
    HarmanDivisorWindow.remainder (S.filter (fun m : ℕ => X^(109/200:ℝ) < (m:ℝ))) w L R =
      ∑ m ∈ S, w m * highKernel X (floorKernel L R) m := by
  rw [HarmanDivisorWindow.remainder_eq_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  simp only [highKernel, floorKernel]
  split_ifs <;> simp

/-- All small-band singletons disappear, including those containing a short prime. -/
theorem small_inner_high_filter (X s : ℝ) (p d : ℕ) (f : ℕ → ℝ) (w : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : p ∈ smallPrimes X s)
    (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s) :
    (∑ t ∈ innerFamily (level X s/p) s (cappedFourth X s p),
      w * highKernel X f (p*(d*t.prod))) =
      ∑ t ∈ (innerFamily (level X s/p) s (cappedFourth X s p)).filter (fun t => ¬isSingleton t),
        w * highKernel X f (p*(d*t.prod)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hsingle : isSingleton t
  · obtain ⟨q,rfl⟩ := hsingle
    have hm := UpperAfter545SmallSingleton.small_singleton_physical_le_545
      X s p d q hX hs hs1 hlog hp hd ht
    have he := highKernel_eq_zero X f _ hm
    have hs' : isSingleton [q] := ⟨q,rfl⟩
    simp only [hs', not_true_eq_false, ite_false, ←Nat.mul_assoc, he, mul_zero]
  · simp only [hsingle, not_false_eq_true, ite_true]

theorem small_collected_high_eq_remaining (X s : ℝ) (f : ℕ → ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    (∑ m ∈ upperSupport X s (smallPrimes X s) (cappedFourth X s),
      upperCoefficient X s (smallPrimes X s) (cappedFourth X s) m * highKernel X f m) =
      smallRemainingKernel X s f := by
  rw [upperSupport, upperCoefficient, FiniteDivisorFamily.sum_coefficient]
  simp_rw [inflated_kernel, SieveUpperBoxWindow.literal_kernel]
  unfold smallRemainingKernel
  apply Finset.sum_congr rfl
  intro p hp
  have hg := small_geometry X s p hX hs hs1 hlog hp
  congr 1
  · apply Finset.sum_congr rfl
    intro d hd
    exact outer_high_filter X s (cappedFourth X s p) p d f _ hX hs hs1 hlog
      hg.1 hg.2.1 hg.2.2.1 hd
  · apply Finset.sum_congr rfl
    intro d hd
    exact small_inner_high_filter X s p d f _ hX hs hs1 hlog hp hd

/-- The actual complete collected high remainder, with its original lower
sign and both original prime bands. No sector coefficient cap is needed. -/
theorem complete_high_eq_remaining (X s x y : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    MomentSmallRemainder.high X s (109/200) x y =
      lowerHighRemainder X s (x-y) x + largeRemainingRemainder X s (x-y) x +
        smallRemainingRemainder X s (x-y) x := by
  unfold MomentSmallRemainder.high MomentSmallRemainder.highSupport
  simp only [not_le]
  rw [filtered_remainder_kernel]
  rw [PositiveSharpRemainderAnalysisPhysical.support,
    PositiveSharpRemainderAnalysisPhysical.coefficient, FiniteDivisorFamily.sum_coefficient]
  simp only [componentSupports, componentCoefficients, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  rw [large_collected_high_eq_remaining X s _ hX hs hs1 hlog,
    small_collected_high_eq_remaining X s _ hX hs hs1 hlog]
  unfold lowerHighRemainder largeRemainingRemainder smallRemainingRemainder
  rw [filtered_remainder_kernel]
  ring

theorem complete_high_eq_lower_add_upper (X s x y : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    MomentSmallRemainder.high X s (109/200) x y =
      lowerHighRemainder X s (x-y) x + upperRemainingRemainder X s (x-y) x := by
  rw [complete_high_eq_remaining X s x y hX hs hs1 hlog, upperRemainingRemainder]
  ring

theorem negative_part_le (X s x y : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    max (-MomentSmallRemainder.high X s (109/200) x y) 0 ≤
      |lowerHighRemainder X s (x-y) x| + max (-upperRemainingRemainder X s (x-y) x) 0 := by
  rw [complete_high_eq_lower_add_upper X s x y hX hs hs1 hlog]
  have hlow := neg_le_abs (lowerHighRemainder X s (x-y) x)
  have hu := le_max_left (-upperRemainingRemainder X s (x-y) x) 0
  have hu0 := le_max_right (-upperRemainingRemainder X s (x-y) x) 0
  apply max_le <;> linarith [abs_nonneg (lowerHighRemainder X s (x-y) x)]

theorem eventually_complete_high_eq_remaining (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ x y : ℝ,
      MomentSmallRemainder.high X s (109/200) x y =
        lowerHighRemainder X s (x-y) x + largeRemainingRemainder X s (x-y) x +
          smallRemainingRemainder X s (x-y) x := by
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1000)] with X hX hlog
  exact fun x y => complete_high_eq_remaining X s x y hX hs hs1 hlog

run_cmd do
  for decl in [``filtered_remainder_kernel, ``small_inner_high_filter,
      ``small_collected_high_eq_remaining, ``complete_high_eq_remaining,
      ``complete_high_eq_lower_add_upper, ``negative_part_le,
      ``eventually_complete_high_eq_remaining] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "COMPLETE PHYSICAL HIGH REDUCED TO LOWER HIGH AND REMAINING UPPER SECTORS PASSED"

end UpperAfter545Remaining
