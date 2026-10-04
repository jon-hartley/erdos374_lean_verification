import E374.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Field.GeomSum

/-!
# Small asymptotic helpers over natural `X`
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

noncomputable section
open Filter

namespace Erdos374.D35

/-- `X^δ` eventually exceeds any constant. -/
theorem nat_eventually_rpow_gt {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → C < (X : ℝ) ^ δ := by
  have ht : Tendsto (fun X : ℕ => (X : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_gt_atTop C)

/-- `log X` is eventually larger than any constant. -/
theorem nat_eventually_log_gt (C : ℝ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → C < Real.log X := by
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_gt_atTop C)

/-- `C X^a < X^b` eventually, for `a < b`. -/
theorem nat_eventually_rpow_dom {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → C * (X : ℝ) ^ a < (X : ℝ) ^ b := by
  obtain ⟨N, hN⟩ := nat_eventually_rpow_gt (sub_pos.mpr hab) C
  refine ⟨max N 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_right N 1) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have h := hN X (le_trans (le_max_left N 1) hX)
  have hsplit : (X : ℝ) ^ b = (X : ℝ) ^ (b - a) * (X : ℝ) ^ a := by
    rw [← Real.rpow_add hX0]; ring_nf
  rw [hsplit]
  exact mul_lt_mul_of_pos_right h (Real.rpow_pos_of_pos hX0 a)

/-- `C X^a log X < X^b` eventually, for `a < b`. -/
theorem nat_eventually_rpow_log_dom {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → C * (X : ℝ) ^ a * Real.log X < (X : ℝ) ^ b := by
  set d := b - a with hd
  have hd0 : 0 < d := sub_pos.mpr hab
  obtain ⟨N, hN⟩ := nat_eventually_rpow_dom (show a + d / 2 < b by linarith)
    (|C| * (2 / d))
  refine ⟨max N 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_right N 1) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hlog : Real.log X ≤ (X : ℝ) ^ (d / 2) / (d / 2) :=
    Real.log_le_rpow_div hX0.le (by positivity)
  have hXa : 0 < (X : ℝ) ^ a := Real.rpow_pos_of_pos hX0 a
  calc C * (X : ℝ) ^ a * Real.log X ≤ |C| * (X : ℝ) ^ a * Real.log X := by
        apply mul_le_mul_of_nonneg_right _ hlog0
        exact mul_le_mul_of_nonneg_right (le_abs_self C) hXa.le
    _ ≤ |C| * (X : ℝ) ^ a * ((X : ℝ) ^ (d / 2) / (d / 2)) := by
        apply mul_le_mul_of_nonneg_left hlog
        exact mul_nonneg (abs_nonneg C) hXa.le
    _ = |C| * (2 / d) * (X : ℝ) ^ (a + d / 2) := by
        rw [Real.rpow_add hX0]; field_simp
    _ < (X : ℝ) ^ b := hN X (le_trans (le_max_left N 1) hX)

/-- Geometric sums in `ℝ`: `∑_{i<n} r^i ≤ (1-r)⁻¹` for `0 ≤ r < 1`. -/
theorem geom_sum_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ (1 - r)⁻¹ := by
  rw [geom_sum_eq hr1.ne n]
  have h1 : 0 < 1 - r := by linarith
  have hpow : 0 ≤ r ^ n := pow_nonneg hr0 n
  have hr1' : r - 1 ≠ 0 := by linarith
  rw [show (r ^ n - 1) / (r - 1) = (1 - r ^ n) / (1 - r) by
    field_simp; ring]
  rw [div_le_iff₀ h1, inv_mul_cancel₀ h1.ne']
  linarith

/-- Monotonicity of `X ↦ X^θ` in the exponent, for `X ≥ 1`. -/
theorem rpow_le_rpow_of_exp_le {X : ℝ} (hX : 1 ≤ X) {a b : ℝ} (hab : a ≤ b) :
    X ^ a ≤ X ^ b := Real.rpow_le_rpow_of_exponent_le hX hab

/-- Combine finitely many eventual statements: helper for `max`. -/
theorem le_of_max_le_left {a b X : ℕ} (h : max a b ≤ X) : a ≤ X := le_trans (le_max_left a b) h
theorem le_of_max_le_right {a b X : ℕ} (h : max a b ≤ X) : b ≤ X :=
  le_trans (le_max_right a b) h

end Erdos374.D35

end
