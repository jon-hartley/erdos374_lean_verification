import MomentSmallMean

/-! Exact reduction of the full signed-remainder moment to indices above
any fixed exponent below the short-interval exponent. The high-index
moment remains an analytic hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace MomentRemainderReduction
open MomentSmallRemainder MomentSmallMean

theorem full_mean_le (X s a Y : ℝ) (hX : 0<X) (hY : 0≤Y) (hYX : Y≤X) :
    (∫x in Icc X (2*X), (PositiveSharpBoxedCount.signedRemainder X s x (x*Y/X))^2)/X≤
      2*((∫x in Icc X (2*X), (low X s a x (x*Y/X))^2)/X)+
      2*((∫x in Icc X (2*X), (high X s a x (x*Y/X))^2)/X) := by
  have hl := low_square_integrable X s a Y hX hY hYX
  have hh := high_square_integrable X s a Y hX hY hYX
  have hf := PositiveSharpRemainderRegularity.signedRemainder_square_integrable X s Y
  have hc := setIntegral_mono_on hf ((hl.const_mul 2).add (hh.const_mul 2))
    measurableSet_Icc (fun x (_hx : x∈Icc X (2*X)) => by
      change (PositiveSharpBoxedCount.signedRemainder X s x (x*Y/X))^2≤
        2*(low X s a x (x*Y/X))^2+2*(high X s a x (x*Y/X))^2
      rw [split X s a]
      nlinarith [sq_nonneg (low X s a x (x*Y/X)-high X s a x (x*Y/X))])
  change (∫x in Icc X (2*X), (PositiveSharpBoxedCount.signedRemainder X s x (x*Y/X))^2)≤
    ∫x in Icc X (2*X), 2*(low X s a x (x*Y/X))^2+2*(high X s a x (x*Y/X))^2 at hc
  rw [integral_add (hl.const_mul 2) (hh.const_mul 2), integral_const_mul,
    integral_const_mul] at hc
  have hd := div_le_div_of_nonneg_right hc hX.le
  convert hd using 1; ring

theorem eventually_full_mean_of_high (s a β C : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) (haβ : a<β) (hβ : β<1)
    (hhigh : ∀ᶠ X:ℝ in atTop,
      (∫x in Icc X (2*X), (high X s a x (x*(X^β/2)/X))^2)/X≤
        C*(X^β/2)^2/(Real.log X)^A) :
    ∀ᶠ X:ℝ in atTop,
      (∫x in Icc X (2*X),
        (PositiveSharpBoxedCount.signedRemainder X s x (x*(X^β/2)/X))^2)/X≤
        (2+2*C)*(X^β/2)^2/(Real.log X)^A := by
  filter_upwards [eventually_low_mean s a β A hs hs1 haβ hβ,
    PositiveSharpPowerWindow.halfWidth_eventually β hβ, hhigh] with X hl hw hh
  have hX : 0<X := by linarith [hl.1]
  have hY : 0<X^β/2 := hw.1
  have hYX : X^β/2≤X := by
    have hw' : X^β/2≤X/4 := hw.2
    linarith
  have hc := full_mean_le X s a (X^β/2) hX hY.le hYX
  calc
    _ ≤ 2*((∫x in Icc X (2*X), (low X s a x (x*(X^β/2)/X))^2)/X)+
      2*((∫x in Icc X (2*X), (high X s a x (x*(X^β/2)/X))^2)/X) := hc
    _ ≤ 2*((X^β/2)^2/(Real.log X)^A)+2*(C*(X^β/2)^2/(Real.log X)^A) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hl.2 (by norm_num))
        (mul_le_mul_of_nonneg_left hh (by norm_num))
    _ = _ := by ring

run_cmd do
  for decl in [``full_mean_le, ``eventually_full_mean_of_high] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FULL REMAINDER REDUCTION TO HIGH INDICES PASSED"

end MomentRemainderReduction
