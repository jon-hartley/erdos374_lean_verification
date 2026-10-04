import RosserInnerIntegral
import PrimeEulerLogSubstitution
import PrimeEulerRightTransfer

/-! One-sided calculus for the continuous inner Rosser kernel. The join at
parameter three is retained exactly, with an integrable right derivative after
the decreasing logarithmic substitution. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
namespace RosserInnerCalculus
open RosserInnerIntegral PrimeEulerLogSubstitution

def leftDerivative (s : ℝ) : ℝ :=
  if s ≤ 3 then -exp (-2)/s^2 else -exp (1-s)*(s+1)/s^2

def test (A x : ℝ) : ℝ := RosserInnerIntegral.inner (parameter A x)
def derivative (A x : ℝ) : ℝ := leftDerivative (parameter A x)*(-A/(x*(log x)^2))

theorem inner_continuousAt (s : ℝ) (hs : s ≠ 0) : ContinuousAt RosserInnerIntegral.inner s := by
  unfold RosserInnerIntegral.inner
  fun_prop

theorem inner_hasDeriv_left (s : ℝ) (hs : 0 < s) :
    HasDerivWithinAt RosserInnerIntegral.inner (leftDerivative s) (Iio s) s := by
  by_cases h3 : s ≤ 3
  · have h : HasDerivAt (fun t : ℝ => exp (-2)/t) (-exp (-2)/s^2) s := by
      convert! (hasDerivAt_const s (exp (-2))).div (hasDerivAt_id s) hs.ne' using 1
      dsimp
      ring
    rw [leftDerivative, ite_eq_left h3]
    apply h.hasDerivWithinAt.congr
    · intro t ht
      unfold RosserInnerIntegral.inner
      rw [max_eq_left (by linarith [ht.out])]
    · unfold RosserInnerIntegral.inner
      rw [max_eq_left (by linarith)]
  · have h : HasDerivAt (fun t : ℝ => exp (1-t)/t)
        (-exp (1-s)*(s+1)/s^2) s := by
      convert! (((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).exp).div
        (hasDerivAt_id s) hs.ne' using 1
      dsimp
      field_simp
      ring
    have heq : RosserInnerIntegral.inner =ᶠ[𝓝 s] (fun t : ℝ => exp (1-t)/t) := by
      filter_upwards [Ioi_mem_nhds (show (3:ℝ)<s by linarith)] with t ht
      unfold RosserInnerIntegral.inner
      rw [max_eq_right (by linarith [ht.out])]
      congr 2
      ring
    rw [leftDerivative, ite_eq_right h3]
    exact (h.congr_of_eventuallyEq heq).hasDerivWithinAt

theorem leftDerivative_nonpos (s : ℝ) (_hs : 1 ≤ s) : leftDerivative s ≤ 0 := by
  unfold leftDerivative
  split_ifs
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (exp_pos _).le) (sq_nonneg _)
  · exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (exp_pos _).le) (by linarith))
      (sq_nonneg _)

theorem parameter_maps_right (A x : ℝ) (hA : 0 < A) (hx : 1 < x) :
    MapsTo (parameter A) (Ioi x) (Iio (parameter A x)) := by
  intro y hy
  change parameter A y < parameter A x
  unfold parameter
  apply sub_lt_sub_right
  exact div_lt_div_of_pos_left hA (Real.log_pos hx)
    (Real.log_lt_log (by linarith) hy)

theorem test_hasDeriv_right (A x : ℝ) (hA : 0 < A) (hx : 1 < x)
    (hs : 1 ≤ parameter A x) :
    HasDerivWithinAt (test A) (derivative A x) (Ioi x) x := by
  exact (inner_hasDeriv_left (parameter A x) (by linarith)).comp x
    (parameter_hasDerivAt A x hx).hasDerivWithinAt (parameter_maps_right A x hA hx)

theorem derivative_nonneg (A x : ℝ) (hA : 0 < A) (hx : 1 < x)
    (hs : 1 ≤ parameter A x) : 0 ≤ derivative A x := by
  apply mul_nonneg_of_nonpos_of_nonpos (leftDerivative_nonpos _ hs)
  exact div_nonpos_of_nonpos_of_nonneg (by linarith)
    (mul_nonneg (by linarith) (sq_nonneg _))

theorem parameter_ge_one (A a b x : ℝ) (hA : 0 < A) (ha : 1 < a)
    (hr : 2 ≤ A/log b) (hx : x ∈ Icc a b) : 1 ≤ parameter A x := by
  have h := parameter_antitoneOn A a hA.le ha hx.1 (hx.1.trans hx.2) hx.2
  unfold parameter at *
  linarith

theorem test_continuousOn (A a b : ℝ) (hA : 0 < A) (ha : 1 < a)
    (hr : 2 ≤ A/log b) : ContinuousOn (test A) (Icc a b) := by
  intro x hx
  exact ((inner_continuousAt _ (by have h := parameter_ge_one A a b x hA ha hr hx; linarith)).comp
    (parameter_hasDerivAt A x (ha.trans_le hx.1)).continuousAt).continuousWithinAt

theorem derivative_intervalIntegrable (A a b : ℝ) (hA : 0 < A) (ha : 1 < a)
    (hab : a ≤ b) (hr : 2 ≤ A/log b) : IntervalIntegrable (derivative A) volume a b := by
  classical
  let lo := fun x : ℝ => (-exp (-2)/(parameter A x)^2)*(-A/(x*(log x)^2))
  let hi := fun x : ℝ => (-exp (1-parameter A x)*(parameter A x+1)/(parameter A x)^2)*
    (-A/(x*(log x)^2))
  have hlo : ContinuousOn lo (Icc a b) := by
    intro x hx
    have hp : 0 < parameter A x := by have h := parameter_ge_one A a b x hA ha hr hx; linarith
    have hxp : 0 < x := by linarith [hx.1]
    have hlp : 0 < log x := log_pos (ha.trans_le hx.1)
    have hc := (parameter_hasDerivAt A x (ha.trans_le hx.1)).continuousAt
    apply ContinuousAt.continuousWithinAt
    dsimp [lo]
    fun_prop (disch := positivity)
  have hhi : ContinuousOn hi (Icc a b) := by
    intro x hx
    have hp : 0 < parameter A x := by have h := parameter_ge_one A a b x hA ha hr hx; linarith
    have hxp : 0 < x := by linarith [hx.1]
    have hlp : 0 < log x := log_pos (ha.trans_le hx.1)
    have hc := (parameter_hasDerivAt A x (ha.trans_le hx.1)).continuousAt
    apply ContinuousAt.continuousWithinAt
    dsimp [hi]
    fun_prop (disch := positivity)
  have hm : MeasurableSet {x : ℝ | parameter A x ≤ 3} := by
    apply measurableSet_le _ measurable_const
    unfold parameter
    fun_prop
  have hloI : IntegrableOn lo (Icc a b) volume := hlo.integrableOn_Icc
  have hhiI : IntegrableOn hi (Icc a b) volume := hhi.integrableOn_Icc
  have h : Integrable ({x : ℝ | parameter A x ≤ 3}.piecewise lo hi)
      (volume.restrict (Icc a b)) :=
    Integrable.piecewise hm hloI.integrableOn hhiI.integrableOn
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have heq : derivative A = {x : ℝ | parameter A x ≤ 3}.piecewise lo hi := by
    ext x
    dsimp [derivative, leftDerivative, Set.piecewise, lo, hi]
    split_ifs <;> rfl
  rw [heq]
  exact h

run_cmd do
  for decl in [``inner_continuousAt, ``inner_hasDeriv_left, ``leftDerivative_nonpos,
    ``parameter_maps_right, ``test_hasDeriv_right, ``derivative_nonneg,
    ``parameter_ge_one, ``test_continuousOn, ``derivative_intervalIntegrable] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end RosserInnerCalculus
end
