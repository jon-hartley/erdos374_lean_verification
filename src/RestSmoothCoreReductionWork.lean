import OuterSmoothApproximationWork
import RestSeparatedCoreReductionWork

/-! Original item 2 reduced to the explicit continuous nine-cutoff core.
The approximation error includes both source and exterior boundaries.
The continuous core's negative mean is still an open analytic target. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace RestSmoothCoreReductionWork
open OuterSmoothCoreWork OuterSmoothApproximationWork LongPairCloseDistinctMeanWork
open LongPairRepeatedCoreMeanWork RestSeparatedCoreReductionWork PositiveSharpPowerWindow

def smoothNegativeMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫x in Icc X (2*X),max (-smoothRemainder X s (x-x*(Y/X)) x) 0)

theorem separated_mean_le_smooth (X s Y : ℝ) (hX : 0<X) :
    separatedCoreNegativeMean X s Y ≤
      (1/X)*(∫x in Icc X (2*X),
        |separatedRemainder X s (x-x*(Y/X)) x-smoothRemainder X s (x-x*(Y/X)) x|)+
      smoothNegativeMean X s Y := by
  have hs := source_moving_integrable (separatedSource X s) X s Y
  change IntegrableOn (fun x => separatedRemainder X s (x-x*(Y/X)) x) _ at hs
  have hm := smooth_moving_integrable X s Y
  have he := (hs.sub hm).abs
  have hi := setIntegral_mono_on hs.neg_part (he.add hm.neg_part) measurableSet_Icc
    (fun x _ => by
      simp only [Pi.add_apply,Pi.sub_apply]
      apply max_le
      · have ha := neg_le_abs (separatedRemainder X s (x-x*(Y/X)) x-
          smoothRemainder X s (x-x*(Y/X)) x)
        have hb := le_max_left (-smoothRemainder X s (x-x*(Y/X)) x) (0:ℝ)
        linarith
      · exact add_nonneg (abs_nonneg _) (le_max_right _ _))
  simp only [Pi.add_apply] at hi
  rw [integral_add he hm.neg_part] at hi
  have hb := mul_le_mul_of_nonneg_left hi (one_div_nonneg.mpr hX.le)
  simpa only [separatedCoreNegativeMean,smoothNegativeMean,mul_add,Pi.sub_apply] using hb

theorem eventually_rest_mean_le_smoothCore (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,
      ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000)) ≤
        9*halfWidth X (101/1000)/(Real.log X)^A+
          smoothNegativeMean X s (halfWidth X (101/1000)) := by
  filter_upwards [eventually_rest_mean_le_separatedCore s A hs hs1,
    eventually_smooth_error_log_unit s A hs hs1] with X hr hf
  have hh := separated_mean_le_smooth X s (halfWidth X (101/1000)) (by linarith [hf.1])
  have hb := hr.trans (add_le_add le_rfl (hh.trans (add_le_add hf.2.2 le_rfl)))
  convert hb using 1 <;> ring

run_cmd do
  for decl in [``separated_mean_le_smooth, ``eventually_rest_mean_le_smoothCore] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end RestSmoothCoreReductionWork
