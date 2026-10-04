import OuterBandSplitWork
import RestCenteredContourReductionWork

/-! The original item-2 mean reduces to central physical frequencies.
Both upper tails are unconditionally negligible after full source assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace RestCentralBandReductionWork
open OuterBandMeanWork OuterBandSplitWork OuterUpperFrequencyWork
open OuterCenteredContourWork RestCenteredContourReductionWork PositiveSharpPowerWindow

def height (X : ℝ) : ℝ := X^(1124/1250:ℝ)
def centralNegativeMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫x in Icc X (2*X),max (-fullBand X s Y (X^(-19/20:ℝ)) (-height X) (height X) x) 0)

theorem eventually_centered_mean_le_central (s : ℝ) (hs : 0≤s) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 256≤X ∧ ∀Y : ℝ, X^(1009/10000:ℝ)≤Y → Y≤X/2 →
      centeredNegativeMean X s Y≤2*Y/(Real.log X)^A+centralNegativeMean X s Y := by
  filter_upwards [eventually_full_upper s hs A,eventually_ge_atTop (Real.exp 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ))] with X ht hX hlog
  refine ⟨ht.1,?_⟩
  intro Y hY hYX
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hX2 : 2≤X := by linarith [ht.1]
  have hY0 : 0≤Y := (Real.rpow_nonneg hXp.le _).trans hY
  have hYX' : Y<X := by linarith
  have hH : 0≤height X := Real.rpow_nonneg hXp.le _
  have hHX : height X≤X := by
    simpa [height] using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤X)
      (show (1124/1250:ℝ)≤1 by norm_num)
  have hε : X^(-19/20:ℝ)∈Ioo 0 1 := ⟨by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith : 1<X) (by norm_num)⟩
  have hi (a b : ℝ) := full_integrable X s Y (X^(-19/20:ℝ)) a b hX hX2 hs hlog hYX' hε
  have he : (fun x => centeredRemainder X s x (Y/X)) =ᵐ[volume.restrict (Icc X (2*X))]
      fullBand X s Y (X^(-19/20:ℝ)) (-X) X := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact centered_eq_full X s Y x hX hX2 hs hlog hx hY0 hYX
  have hic : IntegrableOn (fun x => centeredRemainder X s x (Y/X)) (Icc X (2*X)) :=
    (hi (-X) X).congr he.symm
  have hm := setIntegral_mono_on hic.neg_part
    (((hi (-X) (-height X)).abs.add (hi (-height X) (height X)).neg_part).add (hi (height X) X).abs)
    measurableSet_Icc (fun x hx => by
      simp only [Pi.add_apply]
      rw [centered_three_bands X s Y (height X) x hX hX2 hs hlog hx hY0 hYX hH hHX]
      apply max_le
      · have h1 := neg_le_abs (fullBand X s Y (X^(-19/20:ℝ)) (-X) (-height X) x)
        have h2 := le_max_left (-fullBand X s Y (X^(-19/20:ℝ)) (-height X) (height X) x) (0:ℝ)
        have h3 := neg_le_abs (fullBand X s Y (X^(-19/20:ℝ)) (height X) X x)
        linarith
      · positivity)
  simp only [Pi.add_apply] at hm
  have hs1 := integral_add ((hi (-X) (-height X)).abs.add (hi (-height X) (height X)).neg_part)
      (hi (height X) X).abs
  have hs2 := integral_add (hi (-X) (-height X)).abs (hi (-height X) (height X)).neg_part
  simp only [Pi.add_apply] at hs1 hs2
  rw [hs1,hs2] at hm
  have hl := ht.2 Y (X^(-19/20:ℝ)) (-X) (-height X) hY hYX' hε (by linarith) (by linarith)
    (fun t ht => by
      have hh := neg_le_abs t
      change height X≤|t|
      linarith [ht.2])
  have hr := ht.2 Y (X^(-19/20:ℝ)) (height X) X hY hYX' hε hHX (by linarith)
    (fun t ht => by change height X≤|t|; exact ht.1.trans (le_abs_self t))
  have hh := mul_le_mul_of_nonneg_left hm (one_div_nonneg.mpr hXp.le)
  change (1/X)*(∫x in Icc X (2*X),max (-centeredRemainder X s x (Y/X)) 0)≤_ at hh
  unfold centeredNegativeMean centralNegativeMean
  simp only [mul_add] at hh
  apply hh.trans
  calc
    _ ≤ Y/(Real.log X)^A+(1/X)*(∫x in Icc X (2*X),
        max (-fullBand X s Y (X^(-19/20:ℝ)) (-height X) (height X) x) 0)+Y/(Real.log X)^A :=
      add_le_add (add_le_add hl le_rfl) hr
    _ = _ := by ring

theorem eventually_rest_mean_le_central (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,
      ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000))≤
        15*halfWidth X (101/1000)/(Real.log X)^A+
          centralNegativeMean X s (halfWidth X (101/1000)) := by
  filter_upwards [eventually_rest_mean_le_centered s A hs hs1,
    eventually_centered_mean_le_central s hs.le A,eventually_halfWidth_fits,
    halfWidth_eventually (101/1000) (by norm_num)] with X hrest hcentral hlo hhi
  have hh := hrest.trans (add_le_add le_rfl (hcentral.2 _ hlo (by linarith [hhi.2])))
  apply hh.trans_eq
  ring

run_cmd do
  for decl in [``eventually_centered_mean_le_central, ``eventually_rest_mean_le_central] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end RestCentralBandReductionWork
