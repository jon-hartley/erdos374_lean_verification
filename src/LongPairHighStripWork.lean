import LongPairLargeGeometryWork
import LongPairLargeFlatMeanWork
import RestHighStripReductionWork

/-! Exact signed coefficient family of the only surviving item-2 strip.
Support geometry and subpower caps are proved; its mean remains open. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairHighStripWork
open LongerTupleEncoding LongerTupleCollection LongerTupleActualProfiles
open SieveWeightedCutoffs PositiveSharpBoxedCount UpperAfter545Remaining
open LongPairLargeFlatMeanWork

def highSource (X s : ℝ) : Finset Representation :=
  (LongPairCollectionWork.source X s (largePrimes X) (cutoffThree X s)).filter
    (fun r => X^(26/35:ℝ)<(index r:ℝ))
def highSupport (X s : ℝ) : Finset ℕ := support (highSource X s) index
def highCoefficient (X s : ℝ) (m : ℕ) : ℝ :=
  (coefficient (highSource X s) index (originalWeight X s true) m).re

theorem highRemainder_eq_source (X s L R : ℝ) :
    (largeHighRemainder X s L R:ℂ) =
      ∑ r∈highSource X s,originalWeight X s true r*(floorKernel L R (index r):ℂ) := by
  unfold largeHighRemainder
  rw [LongPairCollectionWork.longPairBand_eq_source]
  simp only [highSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hc : X^(26/35:ℝ)<(index r:ℝ) <;>
    simp only [hc,ite_true,ite_false,Complex.ofReal_zero,mul_zero]

theorem highRemainder_eq_collected (X s L R : ℝ) :
    largeHighRemainder X s L R =
      HarmanDivisorWindow.remainder (highSupport X s) (highCoefficient X s) L R := by
  have hh := congrArg Complex.re
    ((highRemainder_eq_source X s L R).trans
      (grouped_sum (highSource X s) index (originalWeight X s true)
        (fun m => (floorKernel L R m:ℂ))).symm)
  rw [HarmanDivisorWindow.remainder_eq_sum]
  simpa only [highSupport,highCoefficient,floorKernel,Complex.ofReal_re,
    Complex.re_sum,Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero] using hh

theorem support_geometry (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤Real.log X) (m : ℕ) (hm : m∈highSupport X s) :
    X^(26/35:ℝ)<(m:ℝ) ∧ (m:ℝ)<X^(27/35-81*s/35:ℝ) := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hr,hcap⟩ := Finset.mem_filter.mp hr
  exact ⟨hcap,LongPairLargeGeometryWork.large_source_upper X s hX hs hs1 hlog r hr⟩

theorem negativeMean_eq_collected (X s Y : ℝ) :
    RestHighStripReductionWork.highStripNegativeMean X s Y =
      (1/X)*(∫ x in Icc X (2*X),
        max (-HarmanDivisorWindow.remainder (highSupport X s) (highCoefficient X s)
          (x-x*(Y/X)) x) 0) := by
  simp only [RestHighStripReductionWork.highStripNegativeMean,highRemainder_eq_collected]

theorem eventually_highCoefficient_cap (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ X : ℝ in atTop, 1≤X ∧ ∀ (s : ℝ) (m : ℕ),
      0<m → (m:ℝ)≤X^2 → |highCoefficient X s m|≤X^δ := by
  filter_upwards [LongerTupleEncoding.eventual_coefficient_cap 2 δ hδ] with X hh
  refine ⟨hh.1,?_⟩
  intro s m hm hcap
  have hb := hh.2 (highSource X s) (originalWeight X s true)
    (fun r hr => ((LongPairCollectionWork.mem_source X s _ _ r).mp
      (Finset.mem_filter.mp hr).1).2.2.2.1)
    (fun r _ => originalWeight_norm_le X s true r) m hm hcap
  exact (Complex.abs_re_le_norm _).trans hb

#print axioms highRemainder_eq_collected
#print axioms support_geometry
run_cmd do
  for decl in [``highRemainder_eq_source, ``highRemainder_eq_collected,
      ``support_geometry, ``negativeMean_eq_collected, ``eventually_highCoefficient_cap] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairHighStripWork
