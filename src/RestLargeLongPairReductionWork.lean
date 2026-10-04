import RestLongPairReductionWork
import LongPairSmallMeanWork

/-! The only remaining item-2 sector is large-band long pairs. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace RestLargeLongPairReductionWork
open LongerTupleSector LongPairCollectionWork RestLongPairReductionWork
open LongPairSmallMeanWork PositiveSharpPowerWindow PositiveSharpBoxedCount
open SieveWeightedCutoffs SieveCappedUpperMainTerms
open UpperAfter545Remaining

def largeLongPairNegativeMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫ x in Icc X (2*X), max (-longPairBand X s (largePrimes X)
    (cutoffThree X s) (floorKernel (x-x*(Y/X)) x)) 0)

theorem longPair_mean_le_large (X s Y : ℝ) (hX : 0<X) :
    longPairNegativeMean X s Y ≤ largeLongPairNegativeMean X s Y +
      (1/X)*(∫ x in Icc X (2*X), |longPairBand X s (smallPrimes X s)
        (cappedFourth X s) (floorKernel (x-x*(Y/X)) x)|) := by
  have hl := (band_moving_integrable X s Y (largePrimes X) (cutoffThree X s)).neg_part
  have hs := (band_moving_integrable X s Y (smallPrimes X s) (cappedFourth X s)).abs
  have hr := (longPair_moving_integrable X s Y).neg_part
  have hi := setIntegral_mono_on hr (hl.add hs) measurableSet_Icc (fun x _ => by
    simp only [Pi.add_apply]
    unfold longPairRemainder
    apply max_le
    · have ha := le_max_left (-longPairBand X s (largePrimes X) (cutoffThree X s)
        (floorKernel (x-x*(Y/X)) x)) (0:ℝ)
      have hb := neg_le_abs (longPairBand X s (smallPrimes X s) (cappedFourth X s)
        (floorKernel (x-x*(Y/X)) x))
      linarith
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _))
  simp only [Pi.add_apply] at hi
  rw [integral_add hl hs] at hi
  have hh := mul_le_mul_of_nonneg_left hi (one_div_nonneg.mpr hX.le)
  simpa only [longPairNegativeMean,largeLongPairNegativeMean,mul_add] using hh

/-- Original item-2 quantity, with every other sector discharged. -/
theorem eventually_rest_mean_le_largeLongPair (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,
      ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000)) ≤
        3*halfWidth X (101/1000)/(Real.log X)^A +
          largeLongPairNegativeMean X s (halfWidth X (101/1000)) := by
  filter_upwards [eventually_rest_mean_le_longPair s A hs hs1,
    eventually_small_longPair_absolute_log_unit s A hs hs1] with X hr hsmall
  have hl := longPair_mean_le_large X s (halfWidth X (101/1000)) (by linarith [hsmall.1])
  have hb := hr.trans (add_le_add le_rfl
    (hl.trans (add_le_add le_rfl hsmall.2.2)))
  convert hb using 1 <;> ring

#print axioms eventually_rest_mean_le_largeLongPair
run_cmd do
  for decl in [``longPair_mean_le_large, ``eventually_rest_mean_le_largeLongPair] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end RestLargeLongPairReductionWork
