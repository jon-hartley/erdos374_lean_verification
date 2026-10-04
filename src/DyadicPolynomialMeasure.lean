import DyadicPolynomialLevel

/-!
Large-value measure on a support spanning a fixed number of doubling
intervals. The full coefficient energy is shared by all blocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace DyadicPolynomialMeasure
open Erdos374.HarmanAnalytic151MeanSquare DirichletLargeValueMeasure DyadicPolynomialLevel

theorem measure_bound (N k : ℕ) (coeff : ℕ → ℂ) (a T E V : ℝ)
    (hN : 1 ≤ N) (hk : 1 ≤ k) (hT : 0 ≤ T) (hE : 0 < E) (hV : 0 < V)
    (henergy : (∑ n ∈ Finset.Ioc N (2 ^ k * N), ‖coeff n‖ ^ 2) ≤ E) :
    volume (levelSet (exponentialSum151 (Finset.Ioc N (2 ^ k * N)) coeff
      (fun n => Real.log n)) a T V) ≤
      ENNReal.ofReal (516 * k * (2 ^ k * N : ℕ) * (1 + Real.log (T + 1)) *
        (E / (V / k) ^ 2 + 1024 ^ 2 * T * E ^ 3 *
          (1 + Real.log ((2 ^ k * N : ℕ) + 1)) / (V / k) ^ 6)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hGT : 0 ≤ 1 + Real.log (T + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
    linarith
  let F : ℕ → ℝ → ℂ := fun j => exponentialSum151
    (Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N)) coeff (fun n => Real.log n)
  let C : ℝ := 516 * (2 ^ k * N : ℕ) * (1 + Real.log (T + 1)) *
    (E / (V / k) ^ 2 + 1024 ^ 2 * T * E ^ 3 *
      (1 + Real.log ((2 ^ k * N : ℕ) + 1)) / (V / k) ^ 6)
  have hlevel : ∀ j ∈ Finset.range k, volume (levelSet (F j) a T (V / k)) ≤
      ENNReal.ofReal C := by
    intro j hj
    have hjk := Finset.mem_range.mp hj
    have hlow : N ≤ 2 ^ j * N := by
      simpa using Nat.mul_le_mul_right N (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)) (n := j))
    have hupp : 2 ^ (j + 1) * N ≤ 2 ^ k * N :=
      Nat.mul_le_mul_right N (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega))
    have hbase : 2 ^ j * N ≤ 2 ^ k * N :=
      Nat.mul_le_mul_right N (Nat.pow_le_pow_right (by norm_num : 0 < 2) hjk.le)
    have hsub : Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N) ⊆ Finset.Ioc N (2 ^ k * N) := by
      intro n hn
      have hh := Finset.mem_Ioc.mp hn
      exact Finset.mem_Ioc.mpr ⟨hlow.trans_lt hh.1, hh.2.trans hupp⟩
    have he : (∑ n ∈ Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N), ‖coeff n‖ ^ 2) ≤ E :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans henergy
    have hh := exponential_measure_bound (2 ^ j * N) (2 ^ j * N) (2 ^ (j + 1) * N)
      coeff a T E (V / k) (hN.trans hlow) le_rfl
      (by rw [pow_succ]; exact le_of_eq (by ring)) hT hE (div_pos hV hkpos) he
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    dsimp [C]
    have hbaseR : ((2 ^ j * N : ℕ) : ℝ) ≤ (2 ^ k * N : ℕ) := by exact_mod_cast hbase
    have hlog : Real.log (((2 ^ j * N : ℕ) : ℝ) + 1) ≤
        Real.log (((2 ^ k * N : ℕ) : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have hGN : 0 ≤ 1 + Real.log (((2 ^ j * N : ℕ) : ℝ) + 1) := by
      have hh := Real.log_nonneg (show 1 ≤ ((2 ^ j * N : ℕ) : ℝ) + 1 by
        linarith [Nat.cast_nonneg (α := ℝ) (2 ^ j * N)])
      linarith
    gcongr
  have hh := level_union_bound k hk F a T V C hlevel
  have heq : (fun t => ∑ j ∈ Finset.range k, F j t) =
      exponentialSum151 (Finset.Ioc N (2 ^ k * N)) coeff (fun n => Real.log n) := by
    funext t
    exact scaled_partition N k (fun n => coeff n * exponentialKernel151 (Real.log n) t)
  rw [heq] at hh
  convert hh using 1
  congr 1
  dsimp [C]
  ring

end DyadicPolynomialMeasure

#print axioms DyadicPolynomialMeasure.measure_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``DyadicPolynomialMeasure.measure_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "DYADIC POLYNOMIAL MEASURE PASSED"
