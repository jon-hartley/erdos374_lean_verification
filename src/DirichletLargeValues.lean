import DirichletGramKernelBound
import SeparatedFrequencyRows

/-!
The finite Halasz-Montgomery bound with its actual off-diagonal kernel
estimated explicitly. Frequencies are separated by at least one and
have diameter at most T. All analytic kernel inputs are proved.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace DirichletLargeValues
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare

theorem harmonic_ceil_bound (T : ℝ) (hT : 0 ≤ T) :
    (harmonic ⌈T⌉₊ : ℝ) ≤ 1 + Real.log (T + 1) := by
  by_cases hz : ⌈T⌉₊ = 0
  · rw [hz]
    simp only [harmonic_zero, Rat.cast_zero]
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
    linarith
  · have hp : (0 : ℝ) < (⌈T⌉₊ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
    have hh := Real.log_le_log hp (Nat.ceil_lt_add_one hT).le
    exact (harmonic_le_one_add_log ⌈T⌉₊).trans (by linarith)

theorem off_diagonal_bound (N lo hi : ℕ) (r : Finset ℝ) (T t : ℝ)
    (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N) (hT : 0 ≤ T)
    (ht : t ∈ r)
    (hsep : ∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|)
    (hdiam : ∀ x ∈ r, ∀ y ∈ r, |x - y| ≤ T) :
    (∑ u ∈ r.erase t, ‖dirichletGramKernel152 (Finset.Ioc lo hi) (t - u)‖) ≤
      128 * N * (1 + Real.log (T + 1)) +
        512 * r.card * Real.sqrt (T * (1 + Real.log ((N : ℝ) + 1))) := by
  classical
  have hG : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by
      linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith
  have hrow := (SeparatedFrequencyRows.inverse_distance_row r T t ht hsep hdiam).trans
    (mul_le_mul_of_nonneg_left (harmonic_ceil_bound T hT) (by norm_num : (0 : ℝ) ≤ 2))
  have hcard : ((r.erase t).card : ℝ) ≤ r.card := by
    exact_mod_cast Finset.card_le_card (Finset.erase_subset t r)
  calc
    _ ≤ ∑ u ∈ r.erase t,
        (64 * N * (1 / |t - u|) +
          512 * Real.sqrt (T * (1 + Real.log ((N : ℝ) + 1)))) := by
      apply Finset.sum_le_sum
      intro u hu
      have hu' := Finset.mem_erase.mp hu
      have hh := DirichletGramKernelBound.dyadic_interval_bound N lo hi (t - u)
        hN hlo hhi (sub_ne_zero.mpr hu'.1.symm)
      apply hh.trans
      apply add_le_add
      · exact le_of_eq (by ring)
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (hdiam t ht u hu'.2) hG)
    _ = 64 * N * (∑ u ∈ r.erase t, 1 / |t - u|) +
        (r.erase t).card * (512 * Real.sqrt (T * (1 + Real.log ((N : ℝ) + 1)))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 64 * N * (2 * (1 + Real.log (T + 1))) +
        r.card * (512 * Real.sqrt (T * (1 + Real.log ((N : ℝ) + 1)))) :=
      add_le_add (mul_le_mul_of_nonneg_left hrow (by positivity))
        (mul_le_mul_of_nonneg_right hcard (by positivity))
    _ = _ := by ring

theorem mean_square_bound (N lo hi : ℕ) (coeff : ℕ → ℂ)
    (r : Finset ℝ) (T : ℝ)
    (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N) (hT : 0 ≤ T)
    (hsep : ∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|)
    (hdiam : ∀ x ∈ r, ∀ y ∈ r, |x - y| ≤ T) :
    (∑ t ∈ r, ‖exponentialSum151 (Finset.Ioc lo hi) coeff
      (fun n => Real.log n) t‖ ^ 2) ≤
        (129 * N * (1 + Real.log (T + 1)) +
          512 * r.card * Real.sqrt (T * (1 + Real.log ((N : ℝ) + 1)))) *
            ∑ n ∈ Finset.Ioc lo hi, ‖coeff n‖ ^ 2 := by
  classical
  let s := Finset.Ioc lo hi
  let R := 128 * N * (1 + Real.log (T + 1)) +
    512 * r.card * Real.sqrt (T * (1 + Real.log ((N : ℝ) + 1)))
  have hlog : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hs : (s.card : ℝ) ≤ N := by
    dsimp [s]
    rw [Nat.card_Ioc]
    exact_mod_cast (show hi - lo ≤ N by omega)
  have hh := finite_halasz_montgomery_offDiagonal152 r (dirichletVector152 s)
    (coefficientVector152 s coeff) (N : ℝ) R (Nat.cast_nonneg N) hR
    (fun t _ => by rw [dirichletVector_norm_sq152]; exact hs)
    (fun t ht => by
      simp only [dirichletVector_gram152]
      exact off_diagonal_bound N lo hi r T t hN hlo hhi hT ht hsep hdiam)
  simp only [dirichletVector_analysis152, coefficientVector_norm_sq152] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  dsimp [R]
  nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ _) hlog]

theorem large_value_energy (N lo hi : ℕ) (coeff : ℕ → ℂ)
    (r : Finset ℝ) (T V : ℝ)
    (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N) (hT : 0 ≤ T)
    (hV : 0 ≤ V)
    (hsep : ∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|)
    (hdiam : ∀ x ∈ r, ∀ y ∈ r, |x - y| ≤ T)
    (hlarge : ∀ t ∈ r, V ≤ ‖exponentialSum151 (Finset.Ioc lo hi)
      coeff (fun n => Real.log n) t‖) :
    (r.card : ℝ) * V ^ 2 ≤
      (129 * N * (1 + Real.log (T + 1)) +
        512 * r.card * Real.sqrt (T * (1 + Real.log ((N : ℝ) + 1)))) *
          ∑ n ∈ Finset.Ioc lo hi, ‖coeff n‖ ^ 2 := by
  apply le_trans _ (mean_square_bound N lo hi coeff r T hN hlo hhi hT hsep hdiam)
  calc
    _ = ∑ _t ∈ r, V ^ 2 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun t ht =>
      pow_le_pow_left₀ hV (hlarge t ht) 2)

end DirichletLargeValues

#print axioms DirichletLargeValues.large_value_energy
run_cmd do
  let axioms ← Lean.collectAxioms ``DirichletLargeValues.large_value_energy
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "DIRICHLET LARGE VALUES PASSED"
