import SingletonCells
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Complex-valued floor discrepancies and their exact one-period step form. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Real ENNReal

namespace PairFourier

def discrepancy (n : ℕ) (h x : ℝ) : ℂ :=
  (SingletonDivisor.discrepancy n x h : ℂ)

theorem discrepancy_norm_le_one (n : ℕ) (h x : ℝ) :
    ‖discrepancy n h x‖ ≤ 1 := by
  simpa only [discrepancy, Complex.norm_real, Real.norm_eq_abs] using
    SingletonDivisor.abs_discrepancy_le_one n x h

theorem discrepancy_measurable (n : ℕ) (h : ℝ) : Measurable (discrepancy n h) :=
  Complex.measurable_ofReal.comp (SingletonDivisor.measurable n h)

theorem discrepancy_memLp (n : ℕ) (h a b : ℝ) (p : ℝ≥0∞) :
    MemLp (discrepancy n h) p (volume.restrict (Ioc a b)) := by
  apply MemLp.of_bound (discrepancy_measurable n h).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (discrepancy_norm_le_one n h)

theorem discrepancy_intervalIntegrable (n : ℕ) (h a b : ℝ) :
    IntervalIntegrable (discrepancy n h) volume a b := by
  constructor <;> exact (discrepancy_memLp n h _ _ 1).integrable le_rfl

theorem discrepancy_periodic (n : ℕ) (hn : 0 < n) (h : ℝ) :
    Function.Periodic (discrepancy n h) (n : ℝ) := by
  intro x
  exact congrArg Complex.ofReal (SingletonDivisor.periodic n hn h x)

/-- On the open period, the only jump is at `n * fract (h/n)`. This includes
arbitrary real widths, with no sign or upper-bound restriction on `h`. -/
theorem discrepancy_step {n : ℕ} (hn : 0 < n) (h x : ℝ)
    (hx0 : 0 ≤ x) (hxn : x < n) :
    SingletonDivisor.discrepancy n x h =
      if x < (n : ℝ) * Int.fract (h/n)
      then 1 - Int.fract (h/n) else -Int.fract (h/n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : 0 ≤ x/(n:ℝ) ∧ x/(n:ℝ) < 1 :=
    ⟨div_nonneg hx0 hnR.le, (div_lt_one hnR).mpr hxn⟩
  have hu : 0 ≤ Int.fract (h/(n:ℝ)) ∧ Int.fract (h/(n:ℝ)) < 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have heq : (⌊h/(n:ℝ)⌋ : ℝ) + Int.fract (h/(n:ℝ)) = h/(n:ℝ) := by
    rw [Int.fract]; ring
  have hf := SingletonCells.floor_shift_cell 0 ⌊h/(n:ℝ)⌋ (x/n)
    (Int.fract (h/n)) 1 hv hu
  simp only [Int.cast_zero, zero_add, Nat.cast_one, div_one,
    zero_sub, Int.ediv_one] at hf
  rw [heq, ← sub_div] at hf
  unfold SingletonDivisor.discrepancy
  rw [Int.floor_eq_zero_iff.mpr hv, hf]
  have hc : x/(n:ℝ) < Int.fract (h/n) ↔ x < (n:ℝ)*Int.fract (h/n) := by
    rw [div_lt_iff₀ hnR, mul_comm]
  simp only [hc]
  split_ifs with hs <;> simp_all only [Int.cast_zero, Int.cast_neg, Int.cast_add,
    Int.cast_one] <;> linarith

end PairFourier
