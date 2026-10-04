import ShortPairMeanWork
import LongPairCollectionWork
import ShortSingletonClosure

/-! Integrate the exact rest partition: the original endpoint's rest mean
is reduced to the long-pair negative mean, with proved negligible errors. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace RestLongPairReductionWork
open LongerTupleSector LongerTupleHigherMeanWork ShortPairMeanWork
open LongerTupleActualProfiles LongPairCollectionWork
open PositiveSharpPowerWindow PositiveSharpBoxedCount SieveWeightedCutoffs
open SieveCappedUpperMainTerms (cappedFourth)
open ShortSingletonSector

def longPairNegativeMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫ x in Icc X (2*X), max (-longPairRemainder X s (x-x*(Y/X)) x) 0)

theorem longPair_moving_integrable (X s Y : ℝ) :
    IntegrableOn (fun x => longPairRemainder X s (x-x*(Y/X)) x) (Icc X (2*X)) := by
  unfold longPairRemainder
  exact (band_moving_integrable X s Y _ _).add (band_moving_integrable X s Y _ _)

theorem rest_mean_le (X s Y : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤Real.log X) :
    ShortSingletonClosure.restNegativeMean X s Y ≤
      (1/X)*(∫ x in Icc X (2*X), |higherRemainder X s (x-x*(Y/X)) x|) +
      (1/X)*(∫ x in Icc X (2*X), |shortPairRemainder X s (x-x*(Y/X)) x|) +
      longPairNegativeMean X s Y := by
  have hlarge := large_band_geometry X s hX hs hs1 hlog
  have hsmall := small_band_geometry X s hX hs hs1 hlog
  have hh : IntegrableOn (fun x => |higherRemainder X s (x-x*(Y/X)) x|)
      (Icc X (2*X)) := by
    unfold higherRemainder
    exact ((higherBand_moving_integrable X s Y _ _ hs hlarge).add
      (higherBand_moving_integrable X s Y _ _ hs hsmall)).abs
  have ht : IntegrableOn (fun x => |shortPairRemainder X s (x-x*(Y/X)) x|)
      (Icc X (2*X)) := by
    unfold shortPairRemainder
    exact ((shortPairBand_moving_integrable X s Y _ _ hs hlarge).add
      (shortPairBand_moving_integrable X s Y _ _ hs hsmall)).abs
  have hl := (longPair_moving_integrable X s Y).neg_part
  have hr := (ShortSingletonClosure.rest_integrable X s Y hX hs hs1 hlog).neg_part
  have hrest : IntegrableOn (fun x => max (-restRemainder X s (x-x*(Y/X)) x) 0)
      (Icc X (2*X)) := by simpa only [IntegrableOn,mul_div_assoc] using hr
  have hi := setIntegral_mono_on hrest ((hh.add ht).add hl) measurableSet_Icc
    (fun x _ => rest_negative_part_le X s (x-x*(Y/X)) x)
  simp only [Pi.add_apply] at hi
  have hadd := integral_add (hh.add ht) hl
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_add hh ht] at hi
  have hm := mul_le_mul_of_nonneg_left hi (one_div_nonneg.mpr (by linarith : 0≤X))
  simpa only [ShortSingletonClosure.restNegativeMean,longPairNegativeMean,
    mul_div_assoc,div_eq_mul_inv,one_div,mul_add,mul_assoc,mul_comm,mul_left_comm,
    one_mul,mul_one] using hm

/-- No long-pair estimate is assumed: this is an unconditional eventual
inequality for the original item-2 quantity. -/
theorem eventually_rest_mean_le_longPair (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,
      ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000)) ≤
        2*halfWidth X (101/1000)/(Real.log X)^A +
          longPairNegativeMean X s (halfWidth X (101/1000)) := by
  filter_upwards [eventually_higher_absolute_log_unit s A hs hs1,
    eventually_shortPair_absolute_log_unit s A hs hs1] with X hh ht
  apply (rest_mean_le X s _ hh.1 hs hs1 hh.2.1).trans
  have hb := add_le_add_right (add_le_add hh.2.2 ht.2.2)
    (longPairNegativeMean X s (halfWidth X (101/1000)))
  convert hb using 1 <;> ring

#print axioms eventually_rest_mean_le_longPair
run_cmd do
  for decl in [``longPair_moving_integrable, ``rest_mean_le,
      ``eventually_rest_mean_le_longPair] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end RestLongPairReductionWork
