import LongPairHighCoreMeanWork
import RestHighStripReductionWork

/-! Original item 2 reduced to the literal high-product core after removing
the proved Harman edge. No estimate for the core is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace RestHighCoreReductionWork
open LongPairHighCoreMeanWork RestHighStripReductionWork PositiveSharpPowerWindow
open LongPairLargeFlatMeanWork

def highCoreNegativeMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫ x in Icc X (2*X),max (-highCoreRemainder X s (x-x*(Y/X)) x) 0)

theorem high_mean_le_core (X s Y : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) :
    highStripNegativeMean X s Y≤
      (1/X)*(∫ x in Icc X (2*X),|highEdgeRemainder X s (x-x*(Y/X)) x|)+
        highCoreNegativeMean X s Y := by
  have hf := (highEdge_moving_integrable X s Y).abs
  have hh := (highCore_moving_integrable X s Y).neg_part
  have hl := (high_moving_integrable X s Y hX hs hs1 hlog).neg_part
  have hi := setIntegral_mono_on hl (hf.add hh) measurableSet_Icc (fun x _ => by
    simp only [Pi.add_apply]
    rw [high_partition]
    apply max_le
    · have ha := neg_le_abs (highEdgeRemainder X s (x-x*(Y/X)) x)
      have hb := le_max_left (-highCoreRemainder X s (x-x*(Y/X)) x) (0:ℝ)
      linarith
    · exact add_nonneg (abs_nonneg _) (le_max_right _ _))
  simp only [Pi.add_apply] at hi
  rw [integral_add hf hh] at hi
  have hb := mul_le_mul_of_nonneg_left hi (one_div_nonneg.mpr (by linarith : 0≤X))
  simpa only [highStripNegativeMean,highCoreNegativeMean,mul_add] using hb

/-- All proved sectors and the new high edge are discharged in the exact
original rest negative mean. Only the selected-prime core survives. -/
theorem eventually_rest_mean_le_highCore (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,
      ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000))≤
        5*halfWidth X (101/1000)/(Real.log X)^A+
          highCoreNegativeMean X s (halfWidth X (101/1000)) := by
  filter_upwards [eventually_rest_mean_le_highStrip s A hs hs1,
    eventually_highEdge_absolute_log_unit s A hs hs1] with X hr hf
  have hh := high_mean_le_core X s (halfWidth X (101/1000)) hf.1 hs hs1 hf.2.1
  have hb := hr.trans (add_le_add le_rfl (hh.trans (add_le_add hf.2.2 le_rfl)))
  convert hb using 1; ring

#print axioms eventually_rest_mean_le_highCore
run_cmd do
  for decl in [``high_mean_le_core, ``eventually_rest_mean_le_highCore] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end RestHighCoreReductionWork
