import DirichletLargeValueMeasure

/-!
Finite dyadic support partitions and a level-set union bound. These
allow the large-values estimate to cover the support of a polynomial power.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace DyadicPolynomialLevel
open Erdos374.HarmanAnalytic151MeanSquare DirichletLargeValueMeasure

theorem scaled_partition (N k : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ Finset.range k,
      ∑ n ∈ Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N), f n) =
      ∑ n ∈ Finset.Ioc N (2 ^ k * N), f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    apply Finset.sum_Ioc_consecutive
    · simpa using Nat.mul_le_mul_right N (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)) (n := k))
    · exact Nat.mul_le_mul_right N (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega))

theorem exists_large_summand (k : ℕ) (hk : 1 ≤ k) (z : ℕ → ℂ) (V : ℝ)
    (hV : V ≤ ‖∑ j ∈ Finset.range k, z j‖) :
    ∃ j ∈ Finset.range k, V / k ≤ ‖z j‖ := by
  by_contra hn
  push Not at hn
  have hsum := Finset.sum_lt_sum_of_nonempty
    (show (Finset.range k).Nonempty by exact Finset.nonempty_range_iff.mpr (by omega)) hn
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hk0] at hsum
  have hh := norm_sum_le (Finset.range k) z
  linarith

theorem level_union_bound (k : ℕ) (hk : 1 ≤ k) (F : ℕ → ℝ → ℂ)
    (a T V C : ℝ)
    (hlevel : ∀ j ∈ Finset.range k, volume (levelSet (F j) a T (V / k)) ≤
      ENNReal.ofReal C) :
    volume (levelSet (fun t => ∑ j ∈ Finset.range k, F j t) a T V) ≤
      ENNReal.ofReal ((k : ℝ) * C) := by
  have hsub : levelSet (fun t => ∑ j ∈ Finset.range k, F j t) a T V ⊆
      ⋃ j ∈ Finset.range k, levelSet (F j) a T (V / k) := by
    intro t ht
    obtain ⟨j, hj, hnorm⟩ := exists_large_summand k hk (fun j => F j t) V ht.2
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, ht.1, hnorm⟩⟩
  calc
    _ ≤ volume (⋃ j ∈ Finset.range k, levelSet (F j) a T (V / k)) := measure_mono hsub
    _ ≤ ∑ j ∈ Finset.range k, volume (levelSet (F j) a T (V / k)) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range k, ENNReal.ofReal C := Finset.sum_le_sum hlevel
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]

end DyadicPolynomialLevel

#print axioms DyadicPolynomialLevel.level_union_bound
run_cmd do
  for decl in [``DyadicPolynomialLevel.scaled_partition, ``DyadicPolynomialLevel.level_union_bound] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "DYADIC POLYNOMIAL LEVEL PASSED"
