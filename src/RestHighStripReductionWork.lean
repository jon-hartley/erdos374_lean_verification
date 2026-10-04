import LongPairLargeFlatMeanWork
import RestLargeLongPairReductionWork

/-! Original item 2 reduced to the exact large-band products above the
proved flat cap. No estimate for that surviving strip is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace RestHighStripReductionWork
open LongPairLargeFlatMeanWork LongPairCollectionWork RestLargeLongPairReductionWork
open LongPairLargeFlatProfileMeanWork LongPairSmallMeanWork LongerTupleActualProfiles
open PositiveSharpPowerWindow PositiveSharpBoxedCount SieveWeightedCutoffs LongerTupleSector
open UpperAfter545Remaining

def highStripNegativeMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫ x in Icc X (2*X), max (-largeHighRemainder X s (x-x*(Y/X)) x) 0)

theorem flat_moving_integrable (X s Y : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) :
    IntegrableOn (fun x => largeFlatRemainder X s (x-x*(Y/X)) x) (Icc X (2*X)) := by
  unfold largeFlatRemainder
  simp_rw [flatBand_eq_profiles X s _ _ hs (large_band_geometry X s hX hs hs1 hlog)]
  exact integrable_finsetSum _ (fun js _ => capped_moving_integrable X s Y _ _ _ true js)

theorem high_moving_integrable (X s Y : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) :
    IntegrableOn (fun x => largeHighRemainder X s (x-x*(Y/X)) x) (Icc X (2*X)) := by
  have he : (fun x => largeHighRemainder X s (x-x*(Y/X)) x) =
      (fun x => longPairBand X s (largePrimes X) (cutoffThree X s)
        (floorKernel (x-x*(Y/X)) x)-largeFlatRemainder X s (x-x*(Y/X)) x) := by
    funext x
    have hh := large_partition X s (x-x*(Y/X)) x
    linarith
  rw [he]
  exact (band_moving_integrable X s Y _ _).sub (flat_moving_integrable X s Y hX hs hs1 hlog)

theorem large_mean_le_high (X s Y : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) :
    largeLongPairNegativeMean X s Y ≤
      (1/X)*(∫ x in Icc X (2*X), |largeFlatRemainder X s (x-x*(Y/X)) x|) +
        highStripNegativeMean X s Y := by
  have hf := (flat_moving_integrable X s Y hX hs hs1 hlog).abs
  have hh := (high_moving_integrable X s Y hX hs hs1 hlog).neg_part
  have hl := (band_moving_integrable X s Y (largePrimes X) (cutoffThree X s)).neg_part
  have hi := setIntegral_mono_on hl (hf.add hh) measurableSet_Icc (fun x _ => by
    simp only [Pi.add_apply]
    rw [large_partition]
    apply max_le
    · have ha := neg_le_abs (largeFlatRemainder X s (x-x*(Y/X)) x)
      have hb := le_max_left (-largeHighRemainder X s (x-x*(Y/X)) x) (0:ℝ)
      linarith
    · exact add_nonneg (abs_nonneg _) (le_max_right _ _))
  simp only [Pi.add_apply] at hi
  rw [integral_add hf hh] at hi
  have hb := mul_le_mul_of_nonneg_left hi (one_div_nonneg.mpr (by linarith : 0≤X))
  simpa only [largeLongPairNegativeMean,highStripNegativeMean,mul_add] using hb

/-- Every previously covered sector is discharged, in the original quantity. -/
theorem eventually_rest_mean_le_highStrip (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,
      ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000)) ≤
        4*halfWidth X (101/1000)/(Real.log X)^A +
          highStripNegativeMean X s (halfWidth X (101/1000)) := by
  filter_upwards [eventually_rest_mean_le_largeLongPair s A hs hs1,
    eventually_largeFlat_absolute_log_unit s A hs hs1] with X hr hf
  have hh := large_mean_le_high X s (halfWidth X (101/1000)) hf.1 hs hs1 hf.2.1
  have hb := hr.trans (add_le_add le_rfl (hh.trans (add_le_add hf.2.2 le_rfl)))
  convert hb using 1; ring

#print axioms eventually_rest_mean_le_highStrip
run_cmd do
  for decl in [``flat_moving_integrable, ``high_moving_integrable,
      ``large_mean_le_high, ``eventually_rest_mean_le_highStrip] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end RestHighStripReductionWork
