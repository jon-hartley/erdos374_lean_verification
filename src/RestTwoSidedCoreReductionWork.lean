import LongPairTwoSidedCoreMeanWork
import RestHighCoreReductionWork

/-! Original item 2 reduced to a literal core with BOTH tuple primes
above X^.229. The two disjoint edges are fully discharged. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace RestTwoSidedCoreReductionWork
open LongPairTwoSidedCoreMeanWork RestHighCoreReductionWork PositiveSharpPowerWindow
open LongPairLargeFlatMeanWork

def twoSidedCoreNegativeMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫ x in Icc X (2*X),max (-twoSidedCoreRemainder X s (x-x*(Y/X)) x) 0)

theorem core_mean_le_twoSided (X s Y : ℝ) (hX : 1<X) :
    RestHighCoreReductionWork.highCoreNegativeMean X s Y≤
      (1/X)*(∫ x in Icc X (2*X),|otherEdgeRemainder X s (x-x*(Y/X)) x|)+
        twoSidedCoreNegativeMean X s Y := by
  have hf := (otherEdge_moving_integrable X s Y).abs
  have hh := (twoSidedCore_moving_integrable X s Y).neg_part
  have hl := (LongPairHighCoreMeanWork.highCore_moving_integrable X s Y).neg_part
  have hi := setIntegral_mono_on hl (hf.add hh) measurableSet_Icc (fun x _ => by
    simp only [Pi.add_apply]
    rw [core_partition]
    apply max_le
    · have ha := neg_le_abs (otherEdgeRemainder X s (x-x*(Y/X)) x)
      have hb := le_max_left (-twoSidedCoreRemainder X s (x-x*(Y/X)) x) (0:ℝ)
      linarith
    · exact add_nonneg (abs_nonneg _) (le_max_right _ _))
  simp only [Pi.add_apply] at hi
  rw [integral_add hf hh] at hi
  have hb := mul_le_mul_of_nonneg_left hi (one_div_nonneg.mpr (by linarith : 0≤X))
  simpa only [RestHighCoreReductionWork.highCoreNegativeMean,twoSidedCoreNegativeMean,mul_add] using hb

/-- All previously proved sectors and both prime edges are discharged.
No fluctuation estimate for the two-sided core is assumed. -/
theorem eventually_rest_mean_le_twoSidedCore (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,
      ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000))≤
        6*halfWidth X (101/1000)/(Real.log X)^A+
          twoSidedCoreNegativeMean X s (halfWidth X (101/1000)) := by
  filter_upwards [RestHighCoreReductionWork.eventually_rest_mean_le_highCore s A hs hs1,
    eventually_otherEdge_absolute_log_unit s A hs hs1] with X hr hf
  have hh := core_mean_le_twoSided X s (halfWidth X (101/1000)) hf.1
  have hb := hr.trans (add_le_add le_rfl (hh.trans (add_le_add hf.2.2 le_rfl)))
  convert hb using 1; ring

#print axioms eventually_rest_mean_le_twoSidedCore
run_cmd do
  for decl in [``core_mean_le_twoSided, ``eventually_rest_mean_le_twoSidedCore] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end RestTwoSidedCoreReductionWork
