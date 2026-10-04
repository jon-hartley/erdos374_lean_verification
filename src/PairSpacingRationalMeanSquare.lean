import PairSpacingMeanSquare
import PairSpacingRational

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos374.PairSpacingRational

open PairSpacingHarmonic PairSpacingMeanSquare PairSpacingKernel

def angularFrequency (p : ℕ × ℤ) : ℝ := 2 * Real.pi * frequency p

def kappa (Q F : ℕ) : ℝ := 1 + Real.log (2 * (F : ℝ) * (Q : ℝ) ^ 2)

theorem angular_separation {Q F : ℕ} {p q : ℕ × ℤ}
    (hp : p ∈ representatives Q F) (hq : q ∈ representatives Q F)
    (hne : angularFrequency p ≠ angularFrequency q) :
    1 / (Q : ℝ) ^ 2 ≤ |angularFrequency p - angularFrequency q| := by
  have hp' := mem_representatives hp
  have hq' := mem_representatives hq
  have hfreq : frequency p ≠ frequency q := by
    intro hh
    exact hne (congrArg (fun x => 2 * Real.pi * x) hh)
  have hsep := rational_separation hp'.1 hq'.1 hp'.2.1 hq'.2.1 hfreq
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  calc
    _ ≤ |frequency p - frequency q| := hsep
    _ ≤ (2 * Real.pi) * |frequency p - frequency q| :=
      le_mul_of_one_le_left (abs_nonneg _) hpi
    _ = _ := by
      rw [angularFrequency, angularFrequency, ← mul_sub,
        abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]

theorem H_mono {M N : ℕ} (h : M ≤ N) : H M ≤ H N := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _ => by positivity)

theorem harmonic_image_le_kappa {Q F : ℕ} (s : Finset (ℕ × ℤ))
    (hsub : s ⊆ representatives Q F) : H (s.image angularFrequency).card ≤ kappa Q F := by
  have hc : (s.image angularFrequency).card ≤ 2 * F * Q ^ 2 :=
    Finset.card_image_le.trans ((Finset.card_le_card hsub).trans (representatives_card_le Q F))
  calc
    _ ≤ H (2 * F * Q ^ 2) := H_mono hc
    _ ≤ 1 + Real.log (2 * F * Q ^ 2 : ℕ) := by
      rw [H_eq_harmonic]
      exact harmonic_le_one_add_log _
    _ = _ := by simp only [kappa, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem collected_rational_mean_square {Q F : ℕ} (s : Finset (ℕ × ℤ))
    (hsub : s ⊆ representatives Q F) (hQ : 1 ≤ Q)
    (b : (ℕ × ℤ) → ℂ) (A T : ℝ) :
    (∫ t in A..(A + T), ‖exponentialSum s b angularFrequency t‖ ^ 2) ≤
      (T + 4 * (Q : ℝ) ^ 2 * kappa Q F) *
        ∑ ξ ∈ s.image angularFrequency, ‖collectedCoefficient s b angularFrequency ξ‖ ^ 2 := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsep : ∀ x ∈ s.image angularFrequency, ∀ y ∈ s.image angularFrequency,
      x ≠ y → 1 / (Q : ℝ) ^ 2 ≤ |x - y| := by
    intro x hx y hy hne
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    exact angular_separation (hsub hp) (hsub hq) hne
  have hbound := collected_mean_square s b angularFrequency (1 / (Q : ℝ) ^ 2)
    A T (by positivity) hsep
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  apply add_le_add_right
  calc
    _ = 4 * (Q : ℝ) ^ 2 * H (s.image angularFrequency).card := by
      simp only [div_div_eq_mul_div, div_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_image_le_kappa s hsub) (by positivity)

theorem physical_mean_square (Q F : ℕ) (hQ : 1 ≤ Q) (b : ℝ → ℂ) (A T : ℝ) :
    (∫ t in A..(A + T),
      ‖exponentialSum (frequencies Q F) b (fun ξ => 2 * Real.pi * ξ) t‖ ^ 2) ≤
      (T + 4 * (Q : ℝ) ^ 2 * kappa Q F) * ∑ ξ ∈ frequencies Q F, ‖b ξ‖ ^ 2 := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hbound := separated_scaled_mean_square (frequencies Q F) b (2*Real.pi)
    (1/(Q:ℝ)^2) A T (by linarith [Real.two_le_pi]) (by positivity)
    (frequencies_separated Q F)
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  apply add_le_add_right
  have hh : H (frequencies Q F).card ≤ kappa Q F := by
    calc
      _ ≤ H (2*F*Q^2) := H_mono (frequencies_card_le Q F)
      _ ≤ 1 + Real.log (2*F*Q^2 : ℕ) := by
        rw [H_eq_harmonic]
        exact harmonic_le_one_add_log _
      _ = _ := by simp only [kappa, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ = 4 * (Q : ℝ)^2 * H (frequencies Q F).card := by
      simp only [div_div_eq_mul_div, div_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

theorem collection_physical_mean_square (Q F : ℕ) (hQ : 1 ≤ Q)
    (b : (ℕ × ℤ) → ℂ) (A T : ℝ) :
    (∫ t in A..(A + T),
      ‖exponentialSum (representatives Q F) b angularFrequency t‖ ^ 2) ≤
      (T + 4 * (Q : ℝ)^2 * kappa Q F) *
        ∑ ξ ∈ frequencies Q F,
          ‖collectedCoefficient (representatives Q F) b frequency ξ‖ ^ 2 := by
  calc
    _ = ∫ t in A..(A + T),
        ‖exponentialSum (frequencies Q F)
          (collectedCoefficient (representatives Q F) b frequency)
          (fun ξ => 2*Real.pi*ξ) t‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [show angularFrequency = fun p => (2*Real.pi)*frequency p from rfl,
        exponentialSum_eq_collected_scaled]
      rfl
    _ ≤ _ := physical_mean_square Q F hQ _ A T

end Erdos374.PairSpacingRational

