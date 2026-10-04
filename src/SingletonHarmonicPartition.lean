import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! An exact finite partition into blocks of length at most `L`.
The last, possibly shorter, block is part of every identity below. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SingletonHarmonicPartition

def blockCount (X L : ℝ) : ℕ := ⌈X / L⌉₊

def point (t X L : ℝ) (j : ℕ) : ℝ := t + min ((j : ℝ) * L) X

theorem point_zero (t X L : ℝ) (hX : 0 ≤ X) : point t X L 0 = t := by
  simp [point, min_eq_left hX]

theorem point_lower (t X L : ℝ) (hX : 0 ≤ X) (hL : 0 ≤ L) (j : ℕ) :
    t ≤ point t X L j := by
  unfold point
  exact le_add_of_nonneg_right (le_min (mul_nonneg (Nat.cast_nonneg j) hL) hX)

theorem point_upper (t X L : ℝ) (j : ℕ) : point t X L j ≤ t + X := by
  exact add_le_add le_rfl (min_le_right _ _)

theorem point_mono (t X L : ℝ) (hL : 0 ≤ L) : Monotone (point t X L) := by
  intro i j hij
  unfold point
  exact add_le_add le_rfl
    (min_le_min_right X (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hL))

theorem block_length_nonneg (t X L : ℝ) (hL : 0 ≤ L) (j : ℕ) :
    0 ≤ point t X L (j + 1) - point t X L j := by
  exact sub_nonneg.mpr (point_mono t X L hL (Nat.le_succ j))

theorem block_length_le (t X L : ℝ) (hL : 0 ≤ L) (j : ℕ) :
    point t X L (j + 1) - point t X L j ≤ L := by
  unfold point
  simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  by_cases hj : (j : ℝ) * L ≤ X
  · rw [min_eq_left hj]
    linarith [min_le_left ((j : ℝ) * L + L) X]
  · rw [min_eq_right (le_of_not_ge hj)]
    linarith [min_le_right ((j : ℝ) * L + L) X]

theorem point_final (t X L : ℝ) (hL : 0 < L) :
    point t X L (blockCount X L) = t + X := by
  have h : X ≤ (blockCount X L : ℝ) * L :=
    (div_le_iff₀ hL).mp (Nat.le_ceil (X / L))
  exact congrArg (fun u : ℝ => t + u) (min_eq_right h)

theorem blockCount_pos (X L : ℝ) (hX : 0 < X) (hL : 0 < L) :
    0 < blockCount X L := by
  exact Nat.one_le_ceil_iff.mpr (div_pos hX hL)

theorem blockCount_le_ratio_add_one (X L : ℝ) (hX : 0 ≤ X) (hL : 0 < L) :
    (blockCount X L : ℝ) ≤ X / L + 1 := by
  exact (Nat.ceil_lt_add_one (div_nonneg hX hL.le)).le

theorem blockCount_le_two_ratio (X L : ℝ) (hL : 0 < L) (hLX : L ≤ X) :
    (blockCount X L : ℝ) ≤ 2 * (X / L) := by
  have hr : 1 ≤ X / L := (le_div_iff₀ hL).mpr (by simpa using hLX)
  have h := blockCount_le_ratio_add_one X L (hL.le.trans hLX) hL
  linarith

theorem sum_block_lengths (t X L : ℝ) (hX : 0 ≤ X) (hL : 0 < L) :
    (∑ j ∈ Finset.range (blockCount X L),
      (point t X L (j + 1) - point t X L j)) = X := by
  have htel : ∀ J : ℕ, (∑ j ∈ Finset.range J,
      (point t X L (j + 1) - point t X L j)) = point t X L J - point t X L 0 := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  rw [htel, point_final t X L hL, point_zero t X L hX]
  ring

theorem block_integrable (f : ℝ → ℝ) (t X L : ℝ) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hf : IntervalIntegrable f volume t (t + X)) (j : ℕ) :
    IntervalIntegrable f volume (point t X L j) (point t X L (j + 1)) := by
  apply hf.mono_set
  apply Set.uIcc_subset_uIcc
  all_goals
    rw [Set.uIcc_of_le (le_add_of_nonneg_right hX)]
    exact ⟨point_lower t X L hX hL _, point_upper t X L _⟩

theorem sum_block_integrals (f : ℝ → ℝ) (t X L : ℝ) (hX : 0 ≤ X) (hL : 0 < L)
    (hf : IntervalIntegrable f volume t (t + X)) :
    (∑ j ∈ Finset.range (blockCount X L),
      ∫ x in point t X L j..point t X L (j + 1), f x) = ∫ x in t..t + X, f x := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := point t X L) (n := blockCount X L)
    (fun j _ => block_integrable f t X L hX hL.le hf j)
  simpa only [point_zero t X L hX, point_final t X L hL] using h

/-- The boundary allowance `C` is paid once for every block, including the last. -/
theorem integral_le_of_blocks (f : ℝ → ℝ) (t X L A C : ℝ) (hX : 0 ≤ X) (hL : 0 < L)
    (hf : IntervalIntegrable f volume t (t + X))
    (hb : ∀ j < blockCount X L,
      (∫ x in point t X L j..point t X L (j + 1), f x) ≤
        A * (point t X L (j + 1) - point t X L j) + C) :
    (∫ x in t..t + X, f x) ≤ A * X + (blockCount X L : ℝ) * C := by
  rw [← sum_block_integrals f t X L hX hL hf]
  calc
    _ ≤ ∑ j ∈ Finset.range (blockCount X L),
        (A * (point t X L (j + 1) - point t X L j) + C) :=
      Finset.sum_le_sum fun j hj => hb j (Finset.mem_range.mp hj)
    _ = A * X + (blockCount X L : ℝ) * C := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_block_lengths t X L hX hL]
      simp

end SingletonHarmonicPartition
