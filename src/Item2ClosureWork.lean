import OuterUnconditionalMiddleMeanWork
import RestMiddleBandReductionWork

/-! Unconditional closure of the original item-2 rest negative mean. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace Item2ClosureWork
open OuterUnconditionalMiddleMeanWork OuterBandMeanWork
open RestMiddleBandReductionWork RestCentralBandReductionWork OuterLowFrequencyWork
open PositiveSharpPowerWindow

theorem eventually_rest (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) (A : ℕ) :
      ∀ᶠ X : ℝ in atTop,
        ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000))≤
          18*halfWidth X (101/1000)/(Real.log X)^A := by
  filter_upwards [eventually_full_middle s hs.le A,eventually_rest_mean_le_middle s A hs hs1,
    halfWidth_eventually (101/1000) (by norm_num),eventually_ge_atTop (Real.exp 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ)),
    PolynomialLogEnvelope.eventually_constant_bound 2 (1124/1250-1/1000) (by norm_num) (by norm_num),
    PolynomialLogEnvelope.eventually_constant_bound 2 (1124/1250) (by norm_num) (by norm_num)]
      with X hm hr hY hX hlog hratio hheight
  let Y := halfWidth X (101/1000)
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hX2 : 2≤X := by linarith [hm.1]
  have hYX : Y<X := by dsimp [Y]; linarith [hY.1,hY.2]
  have hε : X^(-19/20:ℝ)∈Ioo 0 1 := ⟨by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith : 1<X) (by norm_num)⟩
  have hL : 0≤lowHeight X := Real.rpow_nonneg hXp.le _
  have hLH : lowHeight X≤height X := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hlength : 1≤height X-lowHeight X := by
    have hh := mul_le_mul_of_nonneg_right hratio.2 hL
    change 2*X^(1/1000:ℝ)≤X^(1124/1250-1/1000:ℝ)*X^(1/1000:ℝ) at hh
    rw [←Real.rpow_add hXp] at hh
    norm_num only [show (1124/1250-1/1000:ℝ)+1/1000=1124/1250 by ring] at hh
    change 1≤X^(1124/1250:ℝ)-X^(1/1000:ℝ)
    linarith [hheight.2]
  have hleft := hm.2 Y (X^(-19/20:ℝ)) (-height X) (-lowHeight X) hY.1 hYX hε
    (by change 1≤-lowHeight X-(-height X); linarith) (by change -lowHeight X-(-height X)≤height X; linarith)
    (fun t ht => by
      have htn : t≤0 := by linarith [ht.2]
      rw [abs_of_nonpos htn]
      change lowHeight X≤-t ∧ -t≤height X
      constructor <;> linarith [ht.1,ht.2])
  have hright := hm.2 Y (X^(-19/20:ℝ)) (lowHeight X) (height X) hY.1 hYX hε hlength
    (by change height X-lowHeight X≤height X; linarith)
    (fun t ht => by
      rw [abs_of_nonneg (hL.trans ht.1)]
      exact ht)
  have hi (a b : ℝ) := full_integrable X s Y (X^(-19/20:ℝ)) a b hX hX2 hs.le hlog hYX hε
  have him : IntegrableOn (middleRemainder X s Y) (Icc X (2*X)) :=
    (hi (-height X) (-lowHeight X)).add (hi (lowHeight X) (height X))
  have hh := setIntegral_mono_on him.neg_part
    ((hi (-height X) (-lowHeight X)).abs.add (hi (lowHeight X) (height X)).abs)
    measurableSet_Icc (fun x hx => by
      simp only [Pi.add_apply,middleRemainder]
      apply max_le
      · have ha := neg_le_abs (fullBand X s Y (X^(-19/20:ℝ)) (-height X) (-lowHeight X) x)
        have hb := neg_le_abs (fullBand X s Y (X^(-19/20:ℝ)) (lowHeight X) (height X) x)
        linarith
      · positivity)
  have he := integral_add (hi (-height X) (-lowHeight X)).abs (hi (lowHeight X) (height X)).abs
  simp only [Pi.add_apply] at hh he
  rw [he] at hh
  have hmid : middleNegativeMean X s Y≤2*Y/(Real.log X)^A := by
    have hh := mul_le_mul_of_nonneg_left hh (one_div_nonneg.mpr hXp.le)
    simp only [mul_add] at hh
    apply hh.trans
    exact (add_le_add hleft hright).trans_eq (by ring)
  apply (hr.trans (add_le_add le_rfl hmid)).trans_eq
  dsimp [Y]
  ring

theorem item2 (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,
      ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000))≤
        18*halfWidth X (101/1000)/(Real.log X)^2 :=
  eventually_rest s hs hs1 2

/-- The original final theorem now requires only item 1. -/
theorem erdos_conclusions_of_item1 (C_E : ℝ)
    (hE : ∀ᶠ X : ℝ in atTop,
      (∫x in Icc X (2*X), CancellationTransferCenter.sourceResidualAbs X x
        (x*halfWidth X (101/1000)/X))/X≤C_E/(Real.log X)^2) :
    Erdos374.MainStatement ∧
      Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
      ∃c : ℝ,0<c ∧ ∃cutoff : ℕ,∀N : ℕ,cutoff≤N →
        c*(N:ℝ)≤(Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  obtain ⟨s₀,hs₀,hs1,hend⟩ :=
    ShortSingletonClosure.eventually_erdos_conclusions_of_source_and_rest_negative_mean
  have hs : 0<s₀/2 := by positivity
  exact hend (s₀/2) hs (by linarith) C_E 18 hE (item2 (s₀/2) hs (by linarith))

#print axioms item2
#print axioms erdos_conclusions_of_item1

run_cmd do
  for decl in [``eventually_rest, ``item2, ``erdos_conclusions_of_item1] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ITEM 2 CLOSED UNCONDITIONALLY; FINAL ERDOS CONCLUSIONS REQUIRE ONLY ITEM 1"
end Item2ClosureWork
