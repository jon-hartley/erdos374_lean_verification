import DirectMovingPhysicalAdapter
import DirectMovingEnvelope
import DirectMovingBound

/-! Complete signed physical low-band estimate at X^.545. All original
upper and lower representations enter through the collected coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set

namespace DirectMovingPhysicalMoment
open DirectMovingPhysicalAdapter MomentSmallRemainder
open Erdos374

theorem eventually_half_width_bound (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X), low X s (109/200) x (x*Y/X)^2)≤
        Y^2*X^(-(1/250:ℝ)) := by
  filter_upwards [DirectMovingEnvelope.eventually_uniform_bound,
    MomentRemainderSupport.eventually_support_and_coefficient s (1/1000) hs hs1 (by norm_num),
    PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num)]
    with X he hc hhalf
  refine ⟨he.1,?_⟩
  have hXp : 0<X := by linarith [he.1]
  let Q:=⌊X^(109/200:ℝ)⌋₊
  let F:=⌈X^2⌉₊
  let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
  have hQ : 1≤Q := Nat.le_floor (by
    simpa using Real.one_le_rpow he.1.le (by norm_num : (0:ℝ)≤109/200))
  have hQX : (Q:ℝ)≤X^(109/200:ℝ) := Nat.floor_le (Real.rpow_nonneg hXp.le _)
  have hF : 0<F := Nat.one_le_ceil_iff.mpr (sq_pos_of_pos hXp)
  have hYX : 0≤Y ∧ Y≤X := ⟨hhalf.1.le,by have hh:=hhalf.2; linarith⟩
  have hYhalf : Y≤X/2 := by have hh:=hhalf.2; linarith
  have hcoeff : ∀n∈Finset.Icc 1 Q, |lowCoefficient X s n|≤X^(1/1000:ℝ) := by
    intro n _
    exact coefficient_cap X s _ (by positivity) (fun n hn => (hc.2 n hn).2.2) n
  have hbound := DirectMovingBound.moving_bound Q F (lowCoefficient X s)
    (X^(1/1000:ℝ)) X Y hQ hF (by positivity) hXp hhalf.1 hYhalf hcoeff
  rw [intervalIntegral.integral_of_le (by linarith : X≤2*X),
    ←integral_Icc_eq_integral_Ioc] at hbound
  change (1/X)*(∫x in Icc X (2*X),SingletonMoving.remainder (Finset.Icc 1 Q)
    (lowCoefficient X s) x (x*Y/X)^2)≤
      (X^(1/1000:ℝ))^2*DirectMovingEnvelope.proposedBound Q F X Y at hbound
  change (1/X)*(∫x in Icc X (2*X),low X s (109/200) x (x*Y/X)^2)≤_
  rw [moving_square_integral_eq X s Y hXp (fun n hn => (hc.2 n hn).1) hYX]
  exact hbound.trans (he.2 Q hQ hQX)

run_cmd do
  for ax in (←Lean.collectAxioms ``eventually_half_width_bound) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "COMPLETE PHYSICAL LOW BAND .545 M2 SAVING X^(-1/250) PASSED"

end DirectMovingPhysicalMoment
