import MomentSmallRemainder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! A bounded function has small signed integral under a small dilation.
Applied to the centered floor error, this controls the signed bias of every
physical divisor remainder. It is not an absolute-mean or second-moment bound. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set

namespace CancellationDilation

theorem integral_bound (f : ℝ→ℝ) (C a b : ℝ) (ha : 0≤a) (hab : a≤b)
    (hb : ∀x:ℝ, 0≤x → |f x|≤C) :
    |∫x in a..b, f x|≤C*(b-a) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=a) (b:=b) (C:=C) (f:=f) (fun x hx => by
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le hab] at hx
      exact hb x (ha.trans hx.1.le))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hh

theorem dilation_bias (f : ℝ→ℝ) (C X α : ℝ) (hX : 0≤X) (hα : 0<α) (hα1 : α≤1)
    (hf : ∀a b:ℝ, IntervalIntegrable f volume a b)
    (hb : ∀x:ℝ, 0≤x → |f x|≤C) :
    |(∫x in X..2*X, f x)-α⁻¹*(∫x in α*X..α*(2*X), f x)|≤4*C*(1-α)*X := by
  have hAX : 0≤α*X := mul_nonneg hα.le hX
  have hAXX : α*X≤X := by nlinarith
  have hA2X : α*(2*X)≤2*X := by nlinarith
  have hAXB : α*X≤α*(2*X) := by nlinarith
  have hc : 0≤(1-α)/α := div_nonneg (by linarith) hα.le
  have htop := integral_bound f C (α*(2*X)) (2*X) (by positivity) hA2X hb
  have hbot := integral_bound f C (α*X) X hAX hAXX hb
  have hmid := integral_bound f C (α*X) (α*(2*X)) hAX hAXB hb
  have hdiff := intervalIntegral.integral_interval_sub_interval_comm'
    (hf X (2*X)) (hf (α*X) (α*(2*X))) (hf X (α*X))
  have he : (∫x in X..2*X, f x)-α⁻¹*(∫x in α*X..α*(2*X), f x) =
      ((∫x in X..2*X, f x)-(∫x in α*X..α*(2*X), f x))-
        ((1-α)/α)*(∫x in α*X..α*(2*X), f x) := by
    field_simp
    ring
  rw [he, hdiff]
  calc
    _ ≤ |∫x in α*(2*X)..2*X, f x|+|∫x in α*X..X, f x|+
        |((1-α)/α)*(∫x in α*X..α*(2*X), f x)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ C*(2*X-α*(2*X))+C*(X-α*X)+((1-α)/α)*(C*(α*(2*X)-α*X)) := by
      rw [abs_mul, abs_of_nonneg hc]
      exact add_le_add (add_le_add htop hbot) (mul_le_mul_of_nonneg_left hmid hc)
    _ = _ := by field_simp; ring

def centeredFloor (d : ℕ) (x : ℝ) : ℝ := (⌊x/d⌋₊:ℝ)-x/d+1/2

theorem centeredFloor_bound (d : ℕ) (x : ℝ) (hx : 0≤x) :
    |centeredFloor d x|≤1/2 := by
  have hn := Nat.floor_le (div_nonneg hx (Nat.cast_nonneg d))
  have hh := Nat.sub_one_lt_floor (x/(d:ℝ))
  unfold centeredFloor
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem centeredFloor_integrable (d : ℕ) (a b : ℝ) :
    IntervalIntegrable (centeredFloor d) volume a b := by
  have hm : Monotone (fun x:ℝ => (⌊x/d⌋₊:ℝ)) := by
    intro x y hxy
    change (⌊x/d⌋₊:ℝ)≤(⌊y/d⌋₊:ℝ)
    exact_mod_cast Nat.floor_mono (div_le_div_of_nonneg_right hxy (Nat.cast_nonneg d))
  have hc : Continuous (fun x:ℝ => x/d) := by fun_prop
  exact (hm.intervalIntegrable.sub (hc.intervalIntegrable a b)).add intervalIntegrable_const

theorem centeredFloor_difference (d : ℕ) (x α : ℝ) :
    centeredFloor d x-centeredFloor d (α*x) =
      (⌊x/d⌋₊:ℝ)-(⌊α*x/d⌋₊:ℝ)-(x-α*x)/d := by
  unfold centeredFloor
  ring

run_cmd do
  for decl in [``integral_bound, ``dilation_bias, ``centeredFloor_bound,
      ``centeredFloor_integrable, ``centeredFloor_difference] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "BOUNDED DILATION AND CENTERED FLOOR BIAS PASSED"

end CancellationDilation
