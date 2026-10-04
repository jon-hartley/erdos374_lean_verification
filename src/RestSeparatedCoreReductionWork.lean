import LongPairCloseDistinctMeanWork
import RestDistinctCoreReductionWork

/-! The original rest after both prime edges, repeated tuple primes and
close distinct tuple primes. The farther-apart core is kept exactly. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace RestSeparatedCoreReductionWork
open LongPairCloseDistinctMeanWork LongPairRepeatedCoreMeanWork
open RestDistinctCoreReductionWork PositiveSharpPowerWindow

def separatedCoreNegativeMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫ x in Icc X (2*X),max (-separatedRemainder X s (x-x*(Y/X)) x) 0)

theorem distinct_mean_le_separated (X s Y : ℝ) (hX : 1<X) :
    distinctCoreNegativeMean X s Y≤
      (1/X)*(∫ x in Icc X (2*X),|closeRemainder X s (x-x*(Y/X)) x|)+
        separatedCoreNegativeMean X s Y := by
  have hf := (source_moving_integrable (closeSource X s) X s Y).abs
  have hh := (source_moving_integrable (separatedSource X s) X s Y).neg_part
  have hl := (source_moving_integrable (distinctSource X s) X s Y).neg_part
  change IntegrableOn (fun x => |closeRemainder X s (x-x*(Y/X)) x|) _ at hf
  change IntegrableOn (fun x => max (-separatedRemainder X s (x-x*(Y/X)) x) 0) _ at hh
  change IntegrableOn (fun x => max (-distinctRemainder X s (x-x*(Y/X)) x) 0) _ at hl
  have hi := setIntegral_mono_on hl (hf.add hh) measurableSet_Icc (fun x _ => by
    simp only [Pi.add_apply]
    rw [distinct_partition]
    apply max_le
    · have ha := neg_le_abs (closeRemainder X s (x-x*(Y/X)) x)
      have hb := le_max_left (-separatedRemainder X s (x-x*(Y/X)) x) (0:ℝ)
      linarith
    · exact add_nonneg (abs_nonneg _) (le_max_right _ _))
  simp only [Pi.add_apply] at hi
  rw [integral_add hf hh] at hi
  have hb := mul_le_mul_of_nonneg_left hi (one_div_nonneg.mpr (by linarith : 0≤X))
  simpa only [distinctCoreNegativeMean,separatedCoreNegativeMean,mul_add] using hb

/-- Every discarded piece has an unconditional absolute mean estimate.
No estimate for the separated core is assumed. -/
theorem eventually_rest_mean_le_separatedCore (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,
      ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000))≤
        8*halfWidth X (101/1000)/(Real.log X)^A+
          separatedCoreNegativeMean X s (halfWidth X (101/1000)) := by
  filter_upwards [eventually_rest_mean_le_distinctCore s A hs hs1,
    eventually_close_absolute_log_unit s A hs hs1] with X hr hf
  have hh := distinct_mean_le_separated X s (halfWidth X (101/1000)) hf.1
  have hb := hr.trans (add_le_add le_rfl (hh.trans (add_le_add hf.2.2 le_rfl)))
  convert hb using 1; ring

#print axioms eventually_rest_mean_le_separatedCore
run_cmd do
  for decl in [``distinct_mean_le_separated, ``eventually_rest_mean_le_separatedCore] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end RestSeparatedCoreReductionWork
