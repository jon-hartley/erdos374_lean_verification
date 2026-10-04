import PairSpacingOffDiagonal
import PairSpacingKernel

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos374.PairSpacingMeanSquare

open PairSpacingKernel PairSpacingHarmonic

theorem separated_mean_square (s : Finset ℝ) (b : ℝ → ℂ)
    (δ A T : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) :
    (∫ t in A..(A + T), ‖exponentialSum s b id t‖ ^ 2) ≤
      (T + 4 * H s.card / δ) * ∑ x ∈ s, ‖b x‖ ^ 2 := by
  have h := mean_square_error_le s b id A (A + T) (fun _ _ _ _ hh => hh)
  have hoff := offDiagonal_le s b δ hδ hsep
  have hle := (le_abs_self _).trans (h.trans hoff)
  simp only [add_sub_cancel_left] at hle
  nlinarith

theorem separated_scaled_mean_square (s : Finset ℝ) (b : ℝ → ℂ)
    (c δ A T : ℝ) (hc : 1 ≤ c) (hδ : 0 < δ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) :
    (∫ t in A..(A + T), ‖exponentialSum s b (fun x => c*x) t‖ ^ 2) ≤
      (T + 4 * H s.card / δ) * ∑ x ∈ s, ‖b x‖ ^ 2 := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hinj : Set.InjOn (fun x : ℝ => c*x) (s : Set ℝ) := by
    intro x hx y hy hh
    exact mul_left_cancel₀ hc0.ne' hh
  have h := mean_square_error_le s b (fun x => c*x) A (A + T) hinj
  have hrow : (∑ x ∈ s, ∑ y ∈ s.erase x,
      2 * ‖b x‖ * ‖b y‖ / |c*x-c*y|) ≤
      ∑ x ∈ s, ∑ y ∈ s.erase x, 2 * ‖b x‖ * ‖b y‖ / |x-y| := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro y hy
    have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
    have hpos : 0 < |x-y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    apply div_le_div_of_nonneg_left (by positivity) hpos
    rw [← mul_sub, abs_mul, abs_of_pos hc0]
    exact le_mul_of_one_le_left (abs_nonneg _) hc
  have hle := (le_abs_self _).trans (h.trans (hrow.trans (offDiagonal_le s b δ hδ hsep)))
  simp only [add_sub_cancel_left] at hle
  nlinarith

def collectedCoefficient {ι : Type*} (s : Finset ι) (b : ι → ℂ) (ω : ι → ℝ)
    (ξ : ℝ) : ℂ := ∑ i ∈ s.filter (fun i => ω i = ξ), b i

theorem exponentialSum_eq_collected {ι : Type*} (s : Finset ι)
    (b : ι → ℂ) (ω : ι → ℝ) (t : ℝ) :
    exponentialSum s b ω t =
      exponentialSum (s.image ω) (collectedCoefficient s b ω) id t := by
  classical
  unfold exponentialSum collectedCoefficient
  simp only [id_eq, Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem ω hi)
    (fun i => b i * exponentialKernel (ω i) t)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

theorem exponentialSum_eq_collected_scaled {ι : Type*} (s : Finset ι)
    (b : ι → ℂ) (ω : ι → ℝ) (c t : ℝ) :
    exponentialSum s b (fun i => c * ω i) t =
      exponentialSum (s.image ω) (collectedCoefficient s b ω) (fun ξ => c*ξ) t := by
  classical
  unfold exponentialSum collectedCoefficient
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem ω hi)
    (fun i => b i * exponentialKernel (c * ω i) t)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

theorem collected_mean_square {ι : Type*} (s : Finset ι) (b : ι → ℂ) (ω : ι → ℝ)
    (δ A T : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ s.image ω, ∀ y ∈ s.image ω, x ≠ y → δ ≤ |x - y|) :
    (∫ t in A..(A + T), ‖exponentialSum s b ω t‖ ^ 2) ≤
      (T + 4 * H (s.image ω).card / δ) *
        ∑ ξ ∈ s.image ω, ‖collectedCoefficient s b ω ξ‖ ^ 2 := by
  calc
    _ = ∫ t in A..(A + T),
        ‖exponentialSum (s.image ω) (collectedCoefficient s b ω) id t‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [exponentialSum_eq_collected s b ω t]
    _ ≤ _ := separated_mean_square _ _ δ A T hδ hsep

end Erdos374.PairSpacingMeanSquare
