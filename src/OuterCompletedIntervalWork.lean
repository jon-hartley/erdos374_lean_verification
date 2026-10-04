import OuterSeparatedCoreIntervalWork
import LongPairCofactorSwitchWork

/-! The completed-product window preserves fixed-box outer-prime intervals.
The divisor, tuple, and completed cofactor are held fixed throughout. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped BigOperators

namespace OuterCompletedIntervalWork
open LongerTupleEncoding LongerTupleActualProfiles PositiveSharpBoxedCount
open LongPairCloseDistinctMeanWork OuterSeparatedCoreIntervalWork
open OuterPairSourceDecompositionWork

def completedWindow (d a b k : ℕ) (L R : ℝ) (p : ℕ) : Prop :=
  L < (index (p,d,[a,b])*k:ℕ) ∧ (index (p,d,[a,b])*k:ℕ) ≤ R

def completedBoxSource (X s : ℝ) (d a b i j k : ℕ) (L R : ℝ) (p : ℕ) : Prop :=
  coreBoxSource X s d a b i j p ∧ completedWindow d a b k L R p

theorem completedWindow_convex (d a b k p q r : ℕ) (L R : ℝ)
    (hpq : p≤q) (hqr : q≤r)
    (hp : completedWindow d a b k L R p)
    (hr : completedWindow d a b k L R r) : completedWindow d a b k L R q := by
  have hm (u v : ℕ) (huv : u≤v) :
      (index (u,d,[a,b])*k:ℕ) ≤ (index (v,d,[a,b])*k:ℕ) := by
    simpa [index,Nat.mul_assoc] using Nat.mul_le_mul_right (d*(a*b)*k) huv
  have hpqR : ((index (p,d,[a,b])*k:ℕ):ℝ) ≤ (index (q,d,[a,b])*k:ℕ) :=
    by exact_mod_cast hm p q hpq
  have hqrR : ((index (q,d,[a,b])*k:ℕ):ℝ) ≤ (index (r,d,[a,b])*k:ℕ) :=
    by exact_mod_cast hm q r hqr
  exact ⟨hp.1.trans_le hpqR,hqrR.trans hr.2⟩

theorem completedWindow_iff_cofactor (p d a b k : ℕ) (L R : ℝ)
    (hi : 0 < index (p,d,[a,b])) (hL : 0≤L) (hLR : L≤R) :
    completedWindow d a b k L R p ↔
      k∈LongPairCofactorSwitchWork.cofactorWindow (p,d,[a,b]) L R := by
  have hip : (0:ℝ) < index (p,d,[a,b]) := by exact_mod_cast hi
  rw [LongPairCofactorSwitchWork.cofactorWindow,
    SieveDivisorWindow.mem_window_iff _ _ (div_nonneg hL hip.le)
      (div_le_div_of_nonneg_right hLR hip.le)]
  simp only [completedWindow,Nat.cast_mul,div_lt_iff₀ hip,le_div_iff₀ hip,mul_comm]

theorem completed_weight_eq_box_sum (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (p d a b k : ℕ) (L R : ℝ) :
    (if (p,d,[a,b])∈separatedSource X s ∧ completedWindow d a b k L R p then
      originalWeight X s true (p,d,[a,b]) else 0) =
    ∑ ij∈boxPairs s, if completedBoxSource X s d a b ij.1 ij.2 k L R p then
      originalWeight X s true (p,d,[a,b]) else 0 := by
  by_cases hw : completedWindow d a b k L R p
  · simpa only [completedBoxSource,hw,and_true] using
      separated_weight_eq_box_sum X s hX hs hs1 hlog p d a b
  · simp [completedBoxSource,hw]

theorem eventually_completed_box_interval (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ d a b i j k : ℕ, ∀ L R : ℝ, ∃ lo hi : ℕ, ∃ c : ℂ, ‖c‖≤1 ∧
        ∀ p∈largePrimes X,
          (if completedBoxSource X s d a b i j k L R p then
            originalWeight X s true (p,d,[a,b]) else 0) =
          if lo≤p ∧ p≤hi then c else 0 := by
  filter_upwards [eventually_core_box_interval s hs hs1] with X hX
  refine ⟨hX.1,hX.2.1,?_⟩
  intro d a b i j k L R
  let f := fun p => if coreBoxSource X s d a b i j p then
    originalWeight X s true (p,d,[a,b]) else 0
  have hcap : ∀p∈largePrimes X, ‖f p‖≤1 := by
    intro p _
    dsimp [f]
    split_ifs
    · exact originalWeight_norm_le X s true _
    · simp
  obtain ⟨l,h,c,_,hh⟩ := hX.2.2 d a b i j
  obtain ⟨lo,hi,c,hc,he⟩ := OuterPrimeIntervalRestrictionWork.restrict_weighted_interval
    (largePrimes X) f (completedWindow d a b k L R)
    (fun p _ q _ r _ hpq hqr hp hr => completedWindow_convex d a b k p q r L R hpq hqr hp hr)
    hcap ⟨l,h,c,hh⟩
  refine ⟨lo,hi,c,hc,?_⟩
  intro p hp
  have he := he p hp
  by_cases hw : completedWindow d a b k L R p <;>
    by_cases hb : coreBoxSource X s d a b i j p <;>
    simpa [f,completedBoxSource,hw,hb] using he

run_cmd do
  for decl in [``completedWindow_convex, ``completedWindow_iff_cofactor,
      ``completed_weight_eq_box_sum, ``eventually_completed_box_interval] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterCompletedIntervalWork
