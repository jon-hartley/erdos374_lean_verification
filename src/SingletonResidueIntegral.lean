import SingletonResidue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped BigOperators
open MeasureTheory Set

namespace SingletonResidue

/-- The two constant portions of a unit-cell step have their exact lengths. -/
theorem integral_step {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (A B : ℝ) :
    (∫ v in (0 : ℝ)..1, if v < u then A else B) = u * A + (1 - u) * B := by
  let f : ℝ → ℝ := fun v => if v < u then A else B
  have hl : IntervalIntegrable f volume 0 u := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hu0).mpr
    refine (integrableOn_const (C := A) measure_Ioo_lt_top.ne).congr_fun ?_ measurableSet_Ioo
    intro v hv
    simp [f, hv.2]
  have hr : IntervalIntegrable f volume u 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hu1).mpr
    refine (integrableOn_const (C := B) measure_Ioo_lt_top.ne).congr_fun ?_ measurableSet_Ioo
    intro v hv
    simp [f, not_lt.mpr (le_of_lt hv.1)]
  have hleft : (∫ v in (0 : ℝ)..u, f v) = u * A := by
    calc
      _ = ∫ _ in (0 : ℝ)..u, A := by
        apply intervalIntegral.integral_congr_Ioo_of_le hu0
        intro v hv
        simp [f, hv.2]
      _ = u * A := by simp
  have hright : (∫ v in u..1, f v) = (1 - u) * B := by
    calc
      _ = ∫ _ in u..1, B := by
        apply intervalIntegral.integral_congr_Ioo_of_le hu1
        intro v hv
        simp [f, not_lt.mpr (le_of_lt hv.1)]
      _ = (1 - u) * B := by simp
  change (∫ v in (0 : ℝ)..1, f v) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hl hr, hleft, hright]

/-- Fractional-width Bernoulli covariance, including the endpoints `u = 0, 1`. -/
theorem integral_centered_step_sq {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (k : ℤ) :
    (∫ v in (0 : ℝ)..1,
      (((if v < u then k + 1 else k : ℤ) : ℝ) - ((k : ℝ) + u)) ^ 2) =
      u * (1 - u) := by
  have hf : (fun v : ℝ =>
      (((if v < u then k + 1 else k : ℤ) : ℝ) - ((k : ℝ) + u)) ^ 2) =
      (fun v : ℝ => if v < u then (1 - u) ^ 2 else u ^ 2) := by
    funext v
    split_ifs <;> push_cast <;> ring
  rw [hf, integral_step hu0 hu1]
  ring

/-- Exact integral of the finite coprime residue covariance on a unit cell. -/
theorem integral_sum_centered_product {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (k : ℤ) :
    (∫ v in (0 : ℝ)..1,
      ∑ q ∈ Finset.range (a * b),
        ((count a (if v < u then k + 1 else k) q : ℝ) - ((k : ℝ) + u) / a) *
        ((count b (if v < u then k + 1 else k) q : ℝ) - ((k : ℝ) + u) / b)) =
      u * (1 - u) := by
  simp_rw [sum_centered_product ha hb hab]
  exact integral_centered_step_sq hu0 hu1 k

end SingletonResidue
