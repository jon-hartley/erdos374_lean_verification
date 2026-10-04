import SingletonActualEnvelope
import SingletonActualApplication
import SingletonHarmonicMovingBound

/-! The actual aggregate low-small-divisor outer singleton has an unconditional
moving-window second-moment power saving at the actual first cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set

namespace SingletonActualMoment

theorem eventually_half_width_bound (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀z:ℝ, z≤X^(SieveWeightedScalarBudget.alpha s) →
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),
        SingletonActualCollection.remainder X s z (x-x*(Y/X)) x ^2) ≤
          Y^2*X^(-(1/20:ℝ)) := by
  filter_upwards [SingletonActualEnvelope.eventually_bound,
    PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<101/1000)).eventually
      (eventually_ge_atTop (2:ℝ))] with X he hhalf hpow
  refine ⟨he.1,?_⟩
  intro z hz
  have hXp : 0<X := by linarith [he.1]
  let Q:=⌊X^(31/125:ℝ)⌋₊
  let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
  have hQ : 1≤Q := he.2.1
  have hY1 : 1≤Y := by dsimp [Y,PositiveSharpPowerWindow.halfWidth]; linarith
  have hYX : 0≤Y ∧ Y≤X := ⟨hhalf.1.le,by have hh:=hhalf.2; linarith⟩
  have hcoeff : ∀n∈Finset.Icc 1 Q, |SingletonActualCollection.coefficient X s z n|≤1 := by
    intro n _
    exact SingletonActualCollection.coefficient_abs_le_one_at_first_cutoff
      X s z he.1 hs hs1 hz n
  have hbound := SingletonHarmonicMovingBound.moving_bound Q
    (SingletonActualCollection.coefficient X s z) 1 X Y hQ (by norm_num) hXp hY1 hcoeff
  have hinterval :
      (∫x in X..2*X,
        SingletonMoving.remainder (Finset.Icc 1 Q)
          (SingletonActualCollection.coefficient X s z) x (x*Y/X)^2) =
      ∫x in Icc X (2*X),
        SingletonMoving.remainder (Finset.Icc 1 Q)
          (SingletonActualCollection.coefficient X s z) x (x*(Y/X))^2 := by
    rw [intervalIntegral.integral_of_le (by linarith : X≤2*X),←integral_Icc_eq_integral_Ioc]
    simp only [mul_div_assoc]
  rw [hinterval] at hbound
  simp only [one_pow,mul_one] at hbound
  change (1/X)*(∫x in Icc X (2*X),
    SingletonActualCollection.remainder X s z (x-x*(Y/X)) x ^2) ≤Y^2*X^(-(1/20:ℝ))
  rw [SingletonActualApplication.moving_square_integral_eq X s z Y he.1 hs hs1 hz hYX]
  exact hbound.trans he.2.2

run_cmd do
  for ax in (←Lean.collectAxioms ``eventually_half_width_bound) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in actual singleton moment"
  Lean.logInfo "ACTUAL LOW-D SINGLETON M2 POWER SAVING X^(-1/20) PASSED UNCONDITIONALLY"

end SingletonActualMoment
