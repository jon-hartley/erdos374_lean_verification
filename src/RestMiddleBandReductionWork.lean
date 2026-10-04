import RestCentralBandReductionWork
import OuterLowFrequencyWork

/-! The remaining original item-2 mean is confined to the two middle
physical-frequency bands X^.001 <= |t| <= X^.8992. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace RestMiddleBandReductionWork
open OuterBandMeanWork OuterBandSplitWork OuterLowFrequencyWork
open RestCentralBandReductionWork PositiveSharpPowerWindow

def middleRemainder (X s Y x : ℝ) : ℝ :=
  fullBand X s Y (X^(-19/20:ℝ)) (-height X) (-lowHeight X) x+
    fullBand X s Y (X^(-19/20:ℝ)) (lowHeight X) (height X) x

def middleNegativeMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫x in Icc X (2*X),max (-middleRemainder X s Y x) 0)

theorem central_identity (X s Y x : ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hx : 0<x) (hYX : Y<X) :
    fullBand X s Y (X^(-19/20:ℝ)) (-height X) (height X) x=
      fullBand X s Y (X^(-19/20:ℝ)) (-lowHeight X) (lowHeight X) x+middleRemainder X s Y x := by
  have hXp : 0<X := by linarith
  have hL : 0≤lowHeight X := Real.rpow_nonneg hXp.le _
  have hLH : lowHeight X≤height X :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hε : X^(-19/20:ℝ)∈Ioo 0 1 := ⟨by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith : 1<X) (by norm_num)⟩
  rw [full_adjacent X s Y _ (-height X) (-lowHeight X) (height X) x hX hX2 hs hlog hx hYX hε
      (by linarith) (by linarith),
    full_adjacent X s Y _ (-lowHeight X) (lowHeight X) (height X) x hX hX2 hs hlog hx hYX hε
      (by linarith) hLH]
  unfold middleRemainder
  ring

theorem eventually_central_mean_le_middle (s : ℝ) (hs : 0≤s) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 2≤X ∧ ∀Y : ℝ, 0<Y → Y<X →
      centralNegativeMean X s Y≤Y/(Real.log X)^A+middleNegativeMean X s Y := by
  filter_upwards [eventually_full_low s hs A,eventually_ge_atTop (Real.exp 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ))] with X ht hX hlog
  refine ⟨ht.1,?_⟩
  intro Y hY hYX
  have hXp : 0<X := by linarith [ht.1]
  have hε : X^(-19/20:ℝ)∈Ioo 0 1 := ⟨by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith [ht.1] : 1<X) (by norm_num)⟩
  have hi (a b : ℝ) := full_integrable X s Y (X^(-19/20:ℝ)) a b hX ht.1 hs hlog hYX hε
  have him : IntegrableOn (middleRemainder X s Y) (Icc X (2*X)) :=
    (hi (-height X) (-lowHeight X)).add (hi (lowHeight X) (height X))
  have hm := setIntegral_mono_on (hi (-height X) (height X)).neg_part
    ((hi (-lowHeight X) (lowHeight X)).abs.add him.neg_part) measurableSet_Icc (fun x hx => by
      simp only [Pi.add_apply]
      rw [central_identity X s Y x hX ht.1 hs hlog (hXp.trans_le hx.1) hYX]
      apply max_le
      · have hh := neg_le_abs (fullBand X s Y (X^(-19/20:ℝ)) (-lowHeight X) (lowHeight X) x)
        have hn := le_max_left (-middleRemainder X s Y x) (0:ℝ)
        linarith
      · positivity)
  have he := integral_add (hi (-lowHeight X) (lowHeight X)).abs him.neg_part
  simp only [Pi.add_apply] at hm he
  rw [he] at hm
  have hh := mul_le_mul_of_nonneg_left hm (one_div_nonneg.mpr hXp.le)
  have hl := ht.2 Y (X^(-19/20:ℝ)) hY hYX hε
  simp only [mul_add] at hh
  unfold centralNegativeMean middleNegativeMean
  exact hh.trans (add_le_add hl le_rfl)

theorem eventually_rest_mean_le_middle (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,
      ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000))≤
        16*halfWidth X (101/1000)/(Real.log X)^A+
          middleNegativeMean X s (halfWidth X (101/1000)) := by
  filter_upwards [eventually_rest_mean_le_central s A hs hs1,
    eventually_central_mean_le_middle s hs.le A,
    halfWidth_eventually (101/1000) (by norm_num)] with X hrest hmiddle hhi
  have hh := hrest.trans (add_le_add le_rfl (hmiddle.2 _ hhi.1 (by linarith [hhi.1,hhi.2])))
  apply hh.trans_eq
  ring

run_cmd do
  for decl in [``central_identity, ``eventually_central_mean_le_middle, ``eventually_rest_mean_le_middle] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end RestMiddleBandReductionWork
