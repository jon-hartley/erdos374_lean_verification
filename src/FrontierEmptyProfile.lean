import FrontierSieveEnumeration
import MomentSmallRemainder
import PositiveSharpPowerWindow

/-! The actual empty inner profile is exactly the small lower bracket.
Its elementary support-cardinality bound yields a pointwise and moving-window
second-moment saving. No analytic moment assumption is used. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace FrontierEmptyProfile
open FrontierSieveEnumeration

theorem empty_eq_small_remainder (X s z L R : ℝ) :
    emptyRemainder X s z L R=HarmanDivisorWindow.remainder
      (SieveUpperBoxWindow.smallCarrier (SieveWeightedCutoffs.level X s) s)
      (SieveSmallWeights.weight ((SieveWeightedCutoffs.level X s)^s)
        ((SieveWeightedCutoffs.level X s)^(s^2)) false) L R := by
  simp only [emptyRemainder,MomentRemainderProfileSplit.profileRemainder,
    List.take_nil,List.drop_nil,HarmanDivisorWindow.remainder_eq_sum]
  rw [MomentRemainderProfileSplit.split_kernel]
  simp [SieveBoxGrouping.fibre]

theorem smallCarrier_card_le (D s : ℝ) (hD : 1<D) (hs : 0<s) (hs1 : s≤1) :
    ((SieveUpperBoxWindow.smallCarrier D s).card:ℝ)≤D^s := by
  have hsub : SieveUpperBoxWindow.smallCarrier D s⊆Finset.Ioc 0 ⌊D^s⌋₊ := by
    intro d hd
    refine Finset.mem_Ioc.mpr ⟨?_,?_⟩
    · exact SieveVectorConvolution.carrier_positive _ _ _
        (SieveSmallWeights.primes_prime _) d hd
    · exact Nat.le_floor (PositiveSharpRemainderSupportGeometry.smallCarrier_lt D s hD hs hs1 d hd).le
  have hc := Finset.card_le_card hsub
  have hc' : ((SieveUpperBoxWindow.smallCarrier D s).card:ℝ)≤(⌊D^s⌋₊:ℝ) := by
    exact_mod_cast (by simpa using hc : (SieveUpperBoxWindow.smallCarrier D s).card≤⌊D^s⌋₊)
  exact hc'.trans (Nat.floor_le (Real.rpow_pos_of_pos (by linarith) s).le)

theorem abs_le_power (X s z L R : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hL : 0≤L) (hR : 0≤R) : |emptyRemainder X s z L R|≤X^(1/1000:ℝ) := by
  let D := SieveWeightedCutoffs.level X s
  have hD : 1<D := Real.one_lt_rpow hX (by linarith)
  rw [empty_eq_small_remainder]
  have hh := MomentSmallRemainder.remainder_le_card
    (SieveUpperBoxWindow.smallCarrier D s)
    (SieveSmallWeights.weight (D^s) (D^(s^2)) false) L R 1
    (SieveVectorConvolution.carrier_positive _ _ _ (SieveSmallWeights.primes_prime _))
    hL hR (fun d _ => SieveSmallWeights.weight_abs_le_one _ _ _ d)
  simp only [mul_one] at hh
  apply hh.trans ((smallCarrier_card_le D s hD hs (by linarith)).trans ?_)
  dsimp [D,SieveWeightedCutoffs.level]
  rw [←Real.rpow_mul (show 0≤X by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hX.le (by nlinarith [sq_nonneg s])

theorem square_integrable (X s z Y : ℝ) (hX : 0<X) (hY : 0≤Y) (hYX : Y≤X) :
    IntegrableOn (fun x => (emptyRemainder X s z (x-x*(Y/X)) x)^2) (Icc X (2*X)) := by
  simp only [empty_eq_small_remainder]
  exact SignedDivisorRegularity.integrable_remainder_square _ _ X (Y/X)
    hX.le ⟨div_nonneg hY hX.le,(div_le_one hX).mpr hYX⟩

theorem mean_square_le (X s z Y : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hY : 0≤Y) (hYX : Y≤X) :
    (1/X)*(∫x in Icc X (2*X),(emptyRemainder X s z (x-x*(Y/X)) x)^2)≤X^(1/500:ℝ) := by
  have hXp : 0<X := by linarith
  have hc : IntegrableOn (fun _ : ℝ => X^(1/500:ℝ)) (Icc X (2*X)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hh := setIntegral_mono_on (square_integrable X s z Y hXp hY hYX)
    hc measurableSet_Icc (fun x hx => ?_)
  · rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith : X≤2*X),smul_eq_mul] at hh
    have hr : (∫x in Icc X (2*X),(emptyRemainder X s z (x-x*(Y/X)) x)^2)/X≤X^(1/500:ℝ) :=
      (div_le_iff₀ hXp).mpr (by nlinarith)
    simpa [div_eq_mul_inv,mul_comm] using hr
  · have hx0 : 0≤x := hXp.le.trans hx.1
    have hleft : 0≤x-x*(Y/X) := sub_nonneg.mpr
      (mul_le_of_le_one_right hx0 ((div_le_one hXp).mpr hYX))
    calc
      _ ≤ (X^(1/1000:ℝ))^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
          (abs_le_power X s z _ x hX hs hs1 hleft hx0) 2
      _ = X^(1/500:ℝ) := by rw [←Real.rpow_mul_natCast hXp.le]; norm_num

theorem eventually_half_width_bound (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀z:ℝ,
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),(emptyRemainder X s z (x-x*(Y/X)) x)^2)
        ≤Y^2*X^(-(1/10:ℝ)) := by
  filter_upwards [PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).eventually (eventually_ge_atTop (4:ℝ)),
    eventually_gt_atTop (1:ℝ)] with X hhalf hpow hX
  refine ⟨hX,?_⟩
  intro z
  have hXp : 0<X := by linarith
  let Y := PositiveSharpPowerWindow.halfWidth X (101/1000)
  have hY : 0<Y := hhalf.1
  have hYX : Y≤X := by have hh : Y≤X/4 := hhalf.2; linarith
  apply (mean_square_le X s z Y hX hs hs1 hY.le hYX).trans
  have he : Y^2*X^(-(1/10:ℝ))=X^(1/500:ℝ)*X^(1/10:ℝ)/4 := by
    dsimp [Y,PositiveSharpPowerWindow.halfWidth]
    calc
      _ = ((X^(101/1000:ℝ))^2*X^(-(1/10:ℝ)))/4 := by ring
      _ = _ := by
        rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_add hXp,←Real.rpow_add hXp]
        norm_num
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hXp.le (1/500:ℝ))
  linarith

run_cmd do
  for decl in [``empty_eq_small_remainder,``smallCarrier_card_le,``abs_le_power,
      ``square_integrable,``mean_square_le,``eventually_half_width_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL EMPTY-PROFILE ELEMENTARY POWER SAVING PASSED"

end FrontierEmptyProfile
