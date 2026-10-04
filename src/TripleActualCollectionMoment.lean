import TripleActualCollection
import TripleActualMoment

/-! The full literal low-small-divisor outer-triple remainder has a moving
second-moment saving, including the actual half-width X^.101/2. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TripleActualCollectionMoment
open TripleActualCollection

theorem eventually_bound (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∃c:ℝ,0<c ∧ ∀ᶠ X:ℝ in atTop,1<X ∧ ∀Y z:ℝ,
      z≤X^(SieveWeightedScalarBudget.alpha s) → X^(1009/10000:ℝ)≤Y → Y≤X/2 →
      (1/X)*(∫x in Icc X (2*X),
        PairActualResidual.remainder X s z (x-x*(Y/X)) x ^2)≤Y^2*X^(-c) := by
  obtain ⟨c,hc,he⟩ := TripleActualMoment.eventually_profile_bound s hs hs1
  have hcard := (tendsto_rpow_atTop (show 0<c/4 by positivity)).eventually
    (eventually_ge_atTop ((TailSieveCovered.candidates s).card:ℝ))
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [he,hcard] with X hb hcard
  refine ⟨hb.1,?_⟩
  intro Y z hz hY hYhalf
  have hX : 0<X := by linarith [hb.1]
  have hY0 : 0≤Y := (Real.rpow_nonneg hX.le _).trans hY
  have hcard' : ((PairActualResidual.family X s).card:ℝ)≤X^(c/4) := by
    have hh : ((PairActualResidual.family X s).card:ℝ)≤
        ((TailSieveCovered.candidates s).card:ℝ) := by
      exact_mod_cast Finset.card_le_card (family_subset_candidates X s)
    exact hh.trans hcard
  have hh := FiniteDivisorFamily.normalized_power_bound (PairActualResidual.family X s)
    (componentSupport X s z) (componentWeight X s z) X Y c hX hY0 (by linarith) hcard'
    (by
      intro a ha
      simpa only [component_remainder] using hb.2 Y z a ha hz hY hYhalf)
  change (1/X)*(∫x in Icc X (2*X),TripleActualCollection.remainder X s z (x-x*(Y/X)) x ^2)≤_ at hh
  simpa only [remainder_eq_actual X s z _ _ hb.1 hs hs1] using hh

theorem eventually_half_width_bound (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∃c:ℝ,0<c ∧ ∀ᶠ X:ℝ in atTop,1<X ∧ ∀z:ℝ,
      z≤X^(SieveWeightedScalarBudget.alpha s) →
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),
        PairActualResidual.remainder X s z (x-x*(Y/X)) x ^2)≤Y^2*X^(-c) := by
  obtain ⟨c,hc,he⟩ := eventually_bound s hs hs1
  refine ⟨c,hc,?_⟩
  filter_upwards [he,PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10000)).eventually
      (eventually_ge_atTop (2:ℝ))] with X hh hhalf hpow
  refine ⟨hh.1,?_⟩
  intro z hz
  apply hh.2 _ z hz _ (by linarith [hhalf.2])
  have hX : 0<X := by linarith [hh.1]
  have hm := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hX.le (1009/10000:ℝ))
  rw [←Real.rpow_add hX,show (1009/10000:ℝ)+1/10000=101/1000 by norm_num] at hm
  dsimp [PositiveSharpPowerWindow.halfWidth]
  linarith

run_cmd do
  for decl in [``eventually_bound,``eventually_half_width_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "COMPLETE ACTUAL LOW-D OUTER-TRIPLE M2 POWER SAVING"

end TripleActualCollectionMoment
