import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

/-! Integer-floor discrepancies: periodicity and bounded integrability hold on
all real intervals, including translated intervals crossing zero. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace SingletonDivisor

def discrepancy (n : ℕ) (x h : ℝ) : ℝ :=
  (⌊x / n⌋ : ℝ) - (⌊(x - h) / n⌋ : ℝ) - h / n

theorem discrepancy_eq_fract (n : ℕ) (x h : ℝ) :
    discrepancy n x h = Int.fract ((x-h)/n) - Int.fract (x/n) := by
  unfold discrepancy Int.fract
  rw [sub_div]
  ring

theorem abs_discrepancy_le_one (n : ℕ) (x h : ℝ) :
    |discrepancy n x h| ≤ 1 := by
  rw [discrepancy_eq_fract]
  have h₁ := Int.fract_nonneg ((x-h)/(n:ℝ))
  have h₂ := Int.fract_lt_one ((x-h)/(n:ℝ))
  have h₃ := Int.fract_nonneg (x/(n:ℝ))
  have h₄ := Int.fract_lt_one (x/(n:ℝ))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem periodic (n : ℕ) (hn : 0<n) (h : ℝ) :
    Function.Periodic (fun x => discrepancy n x h) (n:ℝ) := by
  intro x
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp [discrepancy]
  rw [show (x+(n:ℝ))/(n:ℝ)=x/n+1 by field_simp,
    show (x+(n:ℝ)-h)/(n:ℝ)=(x-h)/n+1 by field_simp; ring,
    Int.floor_add_one, Int.floor_add_one]
  push_cast
  ring

theorem measurable (n : ℕ) (h : ℝ) :
    Measurable (fun x => discrepancy n x h) := by
  unfold discrepancy
  have h₁ : Measurable (fun x : ℝ => (⌊x/(n:ℝ)⌋ : ℝ)) := by fun_prop
  have h₂ : Measurable (fun x : ℝ => (⌊(x-h)/(n:ℝ)⌋ : ℝ)) := by fun_prop
  exact (h₁.sub h₂).sub measurable_const

theorem intervalIntegrable (n : ℕ) (h a b : ℝ) :
    IntervalIntegrable (fun x => discrepancy n x h) volume a b := by
  have hi : IntegrableOn (fun x => discrepancy n x h) (uIcc a b) := by
    apply Measure.integrableOn_of_bounded isCompact_uIcc.measure_lt_top.ne
      (measurable n h).aestronglyMeasurable (M:=1)
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using abs_discrepancy_le_one n x h)
  exact hi.intervalIntegrable

theorem natural_floor_eq (n : ℕ) (x h : ℝ) (hx : 0≤x) (hxh : 0≤x-h) :
    (⌊x/n⌋₊:ℝ) - (⌊(x-h)/n⌋₊:ℝ) - h/n = discrepancy n x h := by
  rw [natCast_floor_eq_intCast_floor (div_nonneg hx (Nat.cast_nonneg n)),
    natCast_floor_eq_intCast_floor (div_nonneg hxh (Nat.cast_nonneg n))]
  rfl

end SingletonDivisor
