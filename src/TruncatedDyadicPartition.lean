import DyadicPolynomialLevel
import NormalizedMeanSquare

/-!
Partition a truncated consecutive support into a fixed number of doubling
blocks. The final block keeps its actual upper endpoint. The mean-square
sum bound retains the cost from all blocks and their cross terms.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace TruncatedDyadicPartition
open Erdos374.HarmanGram152

theorem truncate_sum (lo hi B : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc lo hi, if n ≤ B then f n else 0) =
      ∑ n ∈ Finset.Ioc lo (min hi B), f n := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, le_min_iff]
  omega

theorem sum_partition (lo hi k : ℕ) (f : ℕ → ℂ) (hhi : hi ≤ 2 ^ k * lo) :
    (∑ j ∈ Finset.range k,
      ∑ n ∈ Finset.Ioc (2 ^ j * lo) (min (2 ^ (j + 1) * lo) hi), f n) =
        ∑ n ∈ Finset.Ioc lo hi, f n := by
  have hh := DyadicPolynomialLevel.scaled_partition lo k
    (fun n => if n ≤ hi then f n else 0)
  simp_rw [truncate_sum] at hh
  simpa only [min_eq_right hhi] using hh

theorem flat_polynomial (lo hi k : ℕ) (σ t : ℝ) (hhi : hi ≤ 2 ^ k * lo) :
    (∑ j ∈ Finset.range k,
      verticalDirichlet152
        (Finset.Ioc (2 ^ j * lo) (min (2 ^ (j + 1) * lo) hi))
        (fun _ => 1) σ t) =
      verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t := by
  unfold verticalDirichlet152
  exact sum_partition lo hi k _ hhi

theorem sum_energy_bound (k : ℕ) (F : ℕ → ℝ → ℂ) (a b B : ℝ)
    (hF : ∀ j ∈ Finset.range k, Continuous (F j))
    (hbound : ∀ j ∈ Finset.range k, (∫ t in Icc a b, ‖F j t‖ ^ 2) ≤ B) :
    (∫ t in Icc a b, ‖∑ j ∈ Finset.range k, F j t‖ ^ 2) ≤ (k : ℝ) ^ 2 * B := by
  have hsum : Continuous (fun t => ∑ j ∈ Finset.range k, F j t) :=
    continuous_finsetSum _ hF
  have hsumSq : Continuous (fun t => ∑ j ∈ Finset.range k, ‖F j t‖ ^ 2) :=
    continuous_finsetSum _ (fun j hj => (hF j hj).norm.pow 2)
  calc
    _ ≤ ∫ t in Icc a b, (k : ℝ) * ∑ j ∈ Finset.range k, ‖F j t‖ ^ 2 := by
      apply integral_mono (hsum.norm.pow 2).integrableOn_Icc
        (hsumSq.const_mul (k : ℝ)).integrableOn_Icc
      intro t
      simpa only [Finset.card_range, Pi.pow_apply] using
        Erdos374.ExponentialSum151.norm_sum_sq_le_card_energy
          (Finset.range k) (fun j => F j t)
    _ = (k : ℝ) * ∑ j ∈ Finset.range k, ∫ t in Icc a b, ‖F j t‖ ^ 2 := by
      rw [integral_const_mul, integral_finsetSum]
      intro j hj
      exact (hF j hj).norm.pow 2 |>.integrableOn_Icc
    _ ≤ (k : ℝ) * ∑ _j ∈ Finset.range k, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hbound) (Nat.cast_nonneg k)
    _ = _ := by simp; ring

theorem product_energy_bound (lo hi k : ℕ) (σ a b B : ℝ) (F : ℝ → ℂ)
    (hlo : 1 ≤ lo) (hhi : hi ≤ 2 ^ k * lo) (hF : Continuous F)
    (hbound : ∀ j ∈ Finset.range k,
      (∫ t in Icc a b,
        ‖verticalDirichlet152
          (Finset.Ioc (2 ^ j * lo) (min (2 ^ (j + 1) * lo) hi))
          (fun _ => 1) σ t * F t‖ ^ 2) ≤ B) :
    (∫ t in Icc a b,
      ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t * F t‖ ^ 2) ≤
        (k : ℝ) ^ 2 * B := by
  have heq : (fun t => verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t * F t) =
      (fun t => ∑ j ∈ Finset.range k,
        verticalDirichlet152
          (Finset.Ioc (2 ^ j * lo) (min (2 ^ (j + 1) * lo) hi))
          (fun _ => 1) σ t * F t) := by
    funext t
    rw [← Finset.sum_mul, flat_polynomial lo hi k σ t hhi]
  change (∫ t in Icc a b,
    ‖(fun t => verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t * F t) t‖ ^ 2) ≤ _
  rw [heq]
  apply sum_energy_bound k _ a b B ?_ hbound
  intro j hj
  apply Continuous.mul _ hF
  apply NormalizedMeanSquare.continuous_vertical
  intro n hn
  have hbase : 1 ≤ 2 ^ j * lo :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega))
  have hh := (Finset.mem_Ioc.mp hn).1
  omega

end TruncatedDyadicPartition

#print axioms TruncatedDyadicPartition.product_energy_bound
run_cmd do
  for target in [``TruncatedDyadicPartition.sum_partition,
      ``TruncatedDyadicPartition.flat_polynomial,
      ``TruncatedDyadicPartition.sum_energy_bound,
      ``TruncatedDyadicPartition.product_energy_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "TRUNCATED DYADIC PARTITION PASSED"
