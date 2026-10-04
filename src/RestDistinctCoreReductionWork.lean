import LongPairRepeatedCoreMeanWork
import RestTwoSidedCoreReductionWork

/-! Original item 2 reduced to the literal distinct-prime core after
removing the unconditionally negligible repeated-prime contribution. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace RestDistinctCoreReductionWork
open LongPairRepeatedCoreMeanWork RestTwoSidedCoreReductionWork PositiveSharpPowerWindow
open LongPairLargeFlatMeanWork

def distinctCoreNegativeMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫ x in Icc X (2*X),max (-distinctRemainder X s (x-x*(Y/X)) x) 0)

theorem core_mean_le_distinct (X s Y : ℝ) (hX : 1<X) :
    RestTwoSidedCoreReductionWork.twoSidedCoreNegativeMean X s Y≤
      (1/X)*(∫ x in Icc X (2*X),|repeatedRemainder X s (x-x*(Y/X)) x|)+
        distinctCoreNegativeMean X s Y := by
  have hf := (source_moving_integrable (repeatedSource X s) X s Y).abs
  have hh := (source_moving_integrable (distinctSource X s) X s Y).neg_part
  have hl := (LongPairTwoSidedCoreMeanWork.twoSidedCore_moving_integrable X s Y).neg_part
  change IntegrableOn (fun x => |repeatedRemainder X s (x-x*(Y/X)) x|) _ at hf
  change IntegrableOn (fun x => max (-distinctRemainder X s (x-x*(Y/X)) x) 0) _ at hh
  have hi := setIntegral_mono_on hl (hf.add hh) measurableSet_Icc (fun x _ => by
    simp only [Pi.add_apply]
    rw [core_partition]
    apply max_le
    · have ha := neg_le_abs (repeatedRemainder X s (x-x*(Y/X)) x)
      have hb := le_max_left (-distinctRemainder X s (x-x*(Y/X)) x) (0:ℝ)
      linarith
    · exact add_nonneg (abs_nonneg _) (le_max_right _ _))
  simp only [Pi.add_apply] at hi
  rw [integral_add hf hh] at hi
  have hb := mul_le_mul_of_nonneg_left hi (one_div_nonneg.mpr (by linarith : 0≤X))
  simpa only [RestTwoSidedCoreReductionWork.twoSidedCoreNegativeMean,
    distinctCoreNegativeMean,mul_add] using hb

/-- Both prime edges and repeated tuple primes are discharged.
No fluctuation estimate for the distinct-prime core is assumed. -/
theorem eventually_rest_mean_le_distinctCore (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,
      ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000))≤
        7*halfWidth X (101/1000)/(Real.log X)^A+
          distinctCoreNegativeMean X s (halfWidth X (101/1000)) := by
  filter_upwards [RestTwoSidedCoreReductionWork.eventually_rest_mean_le_twoSidedCore s A hs hs1,
    eventually_repeated_absolute_log_unit s A hs hs1] with X hr hf
  have hh := core_mean_le_distinct X s (halfWidth X (101/1000)) hf.1
  have hb := hr.trans (add_le_add le_rfl (hh.trans (add_le_add hf.2.2 le_rfl)))
  convert hb using 1; ring

#print axioms eventually_rest_mean_le_distinctCore
run_cmd do
  for decl in [``core_mean_le_distinct, ``eventually_rest_mean_le_distinctCore] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end RestDistinctCoreReductionWork
