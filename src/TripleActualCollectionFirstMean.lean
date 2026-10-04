import TripleActualCollectionControlled
import TripleFirstMean

/-! Absolute first-mean bounds for the literal complete lower source.
Every fixed logarithmic saving follows from its second-moment power saving.
No upper-sieve estimate or separate source-residual bound is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace TripleActualCollectionFirstMean
open TripleActualCollectionControlled

theorem eventually_power_bound (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∃c:ℝ,0<c ∧ ∀ᶠ X:ℝ in atTop,1<X ∧ ∀z:ℝ,
      z≤X^(SieveWeightedScalarBudget.alpha s) →
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),
        |SieveBoxedWindow.sourceRemainder (SieveWeightedCutoffs.level X s) s z
          (x-x*(Y/X)) x|)≤Y*X^(-c) := by
  obtain ⟨c0,hc0,he⟩ := TripleActualCollectionControlled.eventually_half_width_bound s hs hs1
  refine ⟨c0/2,by positivity,?_⟩
  filter_upwards [he,PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num)]
    with X hh hhalf
  refine ⟨hh.1,?_⟩
  intro z hz
  let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
  let B:=Y*X^(-(c0/2))
  have hX : 0<X := by linarith [hh.1]
  have hY : 0<Y := hhalf.1
  have hYX : Y≤X := by have ht:Y≤X/4 := hhalf.2; linarith
  have hB : 0<B := mul_pos hY (Real.rpow_pos_of_pos hX _)
  have hBsq : B^2=Y^2*X^(-c0) := by
    dsimp [B]
    rw [mul_pow,←Real.rpow_mul_natCast hX.le]
    rw [show (-(c0/2))*(↑(2:ℕ):ℝ)=-c0 by push_cast; ring]
  have hzD : z≤SieveWeightedCutoffs.level X s := hz.trans
    (SingletonActualCollection.cutoff_le_level X s hh.1.le hs.le hs1)
  have hsquare : (1/X)*(∫x in Icc X (2*X),
      remainder X s z (x-x*(Y/X)) x ^2)≤B^2 := by
    rw [hBsq]
    simpa only [remainder_eq_source X s z _ _ hh.1 hs hs1 hzD] using hh.2 z hz
  have hb := TripleFirstMean.remainder_absolute_mean_le
    (FiniteDivisorFamily.support Finset.univ (componentSupport X s z))
    (FiniteDivisorFamily.coefficient Finset.univ (componentSupport X s z)
      (componentWeight X s z)) X Y B hX hY.le hYX hB hsquare
  change (1/X)*(∫x in Icc X (2*X),|remainder X s z (x-x*(Y/X)) x|)≤B at hb
  simpa only [remainder_eq_source X s z _ _ hh.1 hs hs1 hzD] using hb

theorem eventually_log_bound (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) (A : ℕ) :
    ∀ᶠ X:ℝ in atTop,1<X ∧ ∀z:ℝ,
      z≤X^(SieveWeightedScalarBudget.alpha s) →
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),
        |SieveBoxedWindow.sourceRemainder (SieveWeightedCutoffs.level X s) s z
          (x-x*(Y/X)) x|)≤Y/(Real.log X)^A := by
  obtain ⟨c,hc,he⟩ := eventually_power_bound s hs hs1
  filter_upwards [he,PolynomialLogEnvelope.eventually_bound 1 A c (by norm_num) hc]
    with X hh hlog
  refine ⟨hh.1,?_⟩
  intro z hz
  let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
  have hX : 0<X := by linarith [hh.1]
  have hL : 0<Real.log X := Real.log_pos hh.1
  have hLp : (Real.log X)^A≤X^c := by
    apply (pow_le_pow_left₀ hL.le (show Real.log X≤1+Real.log X by linarith) A).trans
    simpa only [one_mul] using hlog.2
  have hp : X^(-c)≤1/(Real.log X)^A := by
    rw [Real.rpow_neg hX.le,←one_div]
    exact one_div_le_one_div_of_le (pow_pos hL A) hLp
  have hY : 0≤Y := by dsimp [Y,PositiveSharpPowerWindow.halfWidth]; positivity
  calc
    _ ≤ Y*X^(-c) := hh.2 z hz
    _ ≤ Y*(1/(Real.log X)^A) := mul_le_mul_of_nonneg_left hp hY
    _ = Y/(Real.log X)^A := by ring

run_cmd do
  for decl in [``eventually_power_bound,``eventually_log_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "COMPLETE LOWER SOURCE ABSOLUTE FIRST MEAN WITH EVERY FIXED LOG SAVING"

end TripleActualCollectionFirstMean
