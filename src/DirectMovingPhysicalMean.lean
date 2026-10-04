import DirectMovingPhysicalMoment
import TripleFirstMean

/-! Absolute first-mean saving for the complete .545 physical low band.
No high-index or Mangoldt source-residual estimate is assumed here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set

namespace DirectMovingPhysicalMean
open MomentSmallRemainder TailRemainderBand PositiveSharpPowerWindow

theorem eventually_absolute_power (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧
      lowAbsoluteMean X s (109/200) (halfWidth X (101/1000))≤
        halfWidth X (101/1000)*X^(-(1/500:ℝ)) := by
  filter_upwards [DirectMovingPhysicalMoment.eventually_half_width_bound s hs hs1,
    halfWidth_eventually (101/1000) (by norm_num)] with X hb hY
  have hXp : 0<X := by linarith [hb.1]
  let Y:=halfWidth X (101/1000)
  have hYX : Y≤X := by have hh:=hY.2; linarith
  have hsq : (1/X)*(∫x in Icc X (2*X),low X s (109/200) x (x*Y/X)^2)≤
      (Y*X^(-(1/500:ℝ)))^2 := by
    have he : (Y*X^(-(1/500:ℝ)))^2=Y^2*X^(-(1/250:ℝ)) := by
      rw [mul_pow,←Real.rpow_mul_natCast hXp.le]
      norm_num
    rw [he]
    exact hb.2
  have hh := TripleFirstMean.absolute_mean_le
    (fun x => low X s (109/200) x (x*Y/X)) X (Y*X^(-(1/500:ℝ))) hXp
    (mul_pos hY.1 (Real.rpow_pos_of_pos hXp _))
    (low_integrable X s (109/200) Y)
    (MomentSmallMean.low_square_integrable X s (109/200) Y hXp hY.1.le hYX) hsq
  refine ⟨hb.1,?_⟩
  simpa only [lowAbsoluteMean,one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul,Y] using hh

theorem eventually_absolute_log (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧
      lowAbsoluteMean X s (109/200) (halfWidth X (101/1000))≤
        halfWidth X (101/1000)/(Real.log X)^A := by
  filter_upwards [eventually_absolute_power s hs hs1,
    PolynomialLogEnvelope.eventually_bound 1 A (1/500) (by norm_num) (by norm_num),
    halfWidth_eventually (101/1000) (by norm_num)] with X hb he hY
  have hXp : 0<X := by linarith [hb.1]
  have hl : 0<Real.log X := Real.log_pos hb.1
  have hlog : (Real.log X)^A≤X^(1/500:ℝ) := by
    apply le_trans _ he.2
    simp only [one_mul]
    exact pow_le_pow_left₀ hl.le (by linarith) A
  have hunit : X^(-(1/500:ℝ))*(Real.log X)^A≤1 := by
    calc
      _ ≤ X^(-(1/500:ℝ))*X^(1/500:ℝ) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 1 := by rw [←Real.rpow_add hXp]; norm_num
  refine ⟨hb.1,hb.2.trans ?_⟩
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hh := mul_le_mul_of_nonneg_left hunit hY.1.le
  nlinarith

run_cmd do
  for decl in [``eventually_absolute_power,``eventually_absolute_log] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "COMPLETE PHYSICAL LOW BAND .545 ABSOLUTE FIRST MEAN ALL LOG POWERS PASSED"

end DirectMovingPhysicalMean
