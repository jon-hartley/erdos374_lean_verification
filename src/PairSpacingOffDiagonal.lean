import PairSpacingHarmonic

noncomputable section
open scoped BigOperators

namespace Erdos374.PairSpacingHarmonic

theorem row_full_le (s : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|)
    (x : ℝ) (hx : x ∈ s) :
    (∑ y ∈ s, 1 / |x - y|) ≤ 2 * H s.card / δ := by
  have heq : (∑ y ∈ s, 1 / |x - y|) = ∑ y ∈ s.erase x, 1 / |x - y| := by
    rw [← Finset.sum_erase_add s (fun y => 1 / |x - y|) hx]
    simp
  rw [heq]
  exact row_le s δ hδ hsep x hx

theorem offDiagonal_le (s : Finset ℝ) (b : ℝ → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ s, ∑ y ∈ s.erase x, 2 * ‖b x‖ * ‖b y‖ / |x - y|) ≤
      (4 * H s.card / δ) * ∑ x ∈ s, ‖b x‖ ^ 2 := by
  have herase : (∑ x ∈ s, ∑ y ∈ s.erase x, 2 * ‖b x‖ * ‖b y‖ / |x - y|) =
      ∑ x ∈ s, ∑ y ∈ s, 2 * ‖b x‖ * ‖b y‖ / |x - y| := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_erase_add s (fun y => 2 * ‖b x‖ * ‖b y‖ / |x - y|) hx]
    simp
  rw [herase]
  have hsymm : (∑ x ∈ s, ∑ y ∈ s, ‖b y‖ ^ 2 / |x - y|) =
      ∑ x ∈ s, ‖b x‖ ^ 2 * ∑ y ∈ s, 1 / |x - y| := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [abs_sub_comm]
    ring
  have hdiag : (∑ x ∈ s, ∑ y ∈ s, ‖b x‖ ^ 2 / |x - y|) =
      ∑ x ∈ s, ‖b x‖ ^ 2 * ∑ y ∈ s, 1 / |x - y| := by
    simp only [Finset.mul_sum, mul_one_div]
  calc
    _ ≤ ∑ x ∈ s, ∑ y ∈ s, (‖b x‖ ^ 2 + ‖b y‖ ^ 2) / |x - y| := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      apply div_le_div_of_nonneg_right _ (abs_nonneg _)
      nlinarith [sq_nonneg (‖b x‖ - ‖b y‖)]
    _ = 2 * ∑ x ∈ s, ‖b x‖ ^ 2 * ∑ y ∈ s, 1 / |x - y| := by
      simp_rw [add_div, Finset.sum_add_distrib]
      rw [hsymm, hdiag]
      ring
    _ ≤ 2 * ∑ x ∈ s, ‖b x‖ ^ 2 * (2 * H s.card / δ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (row_full_le s δ hδ hsep x hx) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end Erdos374.PairSpacingHarmonic
