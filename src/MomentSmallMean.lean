import MomentSmallRemainder
import PositiveSharpPowerWindow
import PositiveSharpRemainderRegularity

/-! For every fixed cutoff exponent a below the interval exponent beta,
the complete small-index contribution has arbitrarily many logarithmic
powers of mean-square saving. No distributional hypothesis is used. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace MomentSmallMean
open MomentSmallRemainder

theorem eventually_low_square (s a β : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) (haβ : a<β) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀x y:ℝ, 0≤x → y≤x →
      (low X s a x y)^2 ≤ (X^β/2)^2/(Real.log X)^A := by
  let ε := (β-a)/2
  have hε : 0<ε := by dsimp [ε]; linarith
  filter_upwards [eventually_low_bound s a ε hs hs1 hε,
    PolynomialLogEnvelope.eventually_bound 4 A (β-a) (by norm_num) (by linarith)]
      with X hb he
  have hX : 0<X := by linarith [hb.1]
  have hl : 0<Real.log X := Real.log_pos hb.1
  have hlog : 4*(Real.log X)^A≤X^(β-a) := by
    apply le_trans _ he.2
    gcongr
    linarith
  refine ⟨hb.1,?_⟩
  intro x y hx hyx
  have hsq : (low X s a x y)^2≤(X^(a+ε))^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb.2 x y hx hyx) 2
  have hprod : (X^(a+ε))^2 * (4*(Real.log X)^A) ≤ (X^β)^2 := by
    calc
      _ ≤ (X^(a+ε))^2 * X^(β-a) := mul_le_mul_of_nonneg_left hlog (sq_nonneg _)
      _ = (X^β)^2 := by
        rw [←Real.rpow_mul_natCast hX.le, ←Real.rpow_add hX,
          ←Real.rpow_mul_natCast hX.le]
        congr 1
        dsimp [ε]
        ring
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hh := mul_le_mul_of_nonneg_right hsq (show 0≤4*(Real.log X)^A by positivity)
  nlinarith

theorem low_square_integrable (X s a Y : ℝ) (hX : 0<X) (hY : 0≤Y) (hYX : Y≤X) :
    IntegrableOn (fun x => (low X s a x (x*Y/X))^2) (Icc X (2*X)) := by
  have hh := SignedDivisorRegularity.integrable_remainder_square
    (lowSupport X s a) (PositiveSharpRemainderAnalysisPhysical.coefficient X s)
    X (Y/X) hX.le ⟨div_nonneg hY hX.le, (div_le_one hX).mpr hYX⟩
  simpa only [low, mul_div_assoc] using hh

theorem high_square_integrable (X s a Y : ℝ) (hX : 0<X) (hY : 0≤Y) (hYX : Y≤X) :
    IntegrableOn (fun x => (high X s a x (x*Y/X))^2) (Icc X (2*X)) := by
  have hh := SignedDivisorRegularity.integrable_remainder_square
    (highSupport X s a) (PositiveSharpRemainderAnalysisPhysical.coefficient X s)
    X (Y/X) hX.le ⟨div_nonneg hY hX.le, (div_le_one hX).mpr hYX⟩
  simpa only [high, mul_div_assoc] using hh

theorem low_mean_of_pointwise (X s a Y B : ℝ) (hX : 0<X) (hY : 0≤Y) (hYX : Y≤X)
    (hb : ∀x∈Icc X (2*X), (low X s a x (x*Y/X))^2≤B) :
    (∫x in Icc X (2*X), (low X s a x (x*Y/X))^2)/X≤B := by
  have hc : IntegrableOn (fun _ : ℝ => B) (Icc X (2*X)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hh := setIntegral_mono_on (low_square_integrable X s a Y hX hY hYX)
    hc measurableSet_Icc hb
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith : X≤2*X), smul_eq_mul] at hh
  exact (div_le_iff₀ hX).mpr (by nlinarith)

theorem eventually_low_mean (s a β : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) (haβ : a<β) (hβ : β<1) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧
      (∫x in Icc X (2*X), (low X s a x (x*(X^β/2)/X))^2)/X≤
        (X^β/2)^2/(Real.log X)^A := by
  filter_upwards [eventually_low_square s a β A hs hs1 haβ,
    PositiveSharpPowerWindow.halfWidth_eventually β hβ] with X hb hw
  have hX : 0<X := by linarith [hb.1]
  have hY : 0<X^β/2 := hw.1
  have hYX : X^β/2≤X := by
    have hw' : X^β/2≤X/4 := hw.2
    linarith
  refine ⟨hb.1, low_mean_of_pointwise X s a (X^β/2) _ hX hY.le hYX ?_⟩
  intro x hx
  have hx0 : 0≤x := hX.le.trans hx.1
  apply hb.2 x _ hx0
  exact (div_le_iff₀ hX).mpr (mul_le_mul_of_nonneg_left hYX hx0)

run_cmd do
  for decl in [``eventually_low_square, ``low_square_integrable, ``high_square_integrable,
      ``low_mean_of_pointwise, ``eventually_low_mean] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SMALL REMAINDER ALL LOGARITHMIC MOMENT SAVINGS PASSED"

end MomentSmallMean
