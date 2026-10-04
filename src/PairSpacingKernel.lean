import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! Finite exponential-polynomial mean squares with explicit off-diagonal
bounds. These are unconditional analytic lemmas, not exceptional-set axioms. -/

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Erdos374.PairSpacingKernel

def exponentialKernel (ω t : ℝ) : ℂ :=
  Complex.exp ((Complex.I * (ω : ℂ)) * (t : ℂ))

def exponentialSum {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ξ : ι → ℝ) (t : ℝ) : ℂ := ∑ n ∈ s, a n * exponentialKernel (ξ n) t

theorem continuous_kernel (ω : ℝ) : Continuous (exponentialKernel ω) := by
  unfold exponentialKernel
  fun_prop

theorem norm_kernel (ω t : ℝ) : ‖exponentialKernel ω t‖ = 1 := by
  simp [exponentialKernel, Complex.norm_exp]

theorem kernel_zero (t : ℝ) : exponentialKernel 0 t = 1 := by
  simp [exponentialKernel]

theorem kernel_mul_conj (ω ν t : ℝ) :
    exponentialKernel ω t * conj (exponentialKernel ν t) =
      exponentialKernel (ω - ν) t := by
  unfold exponentialKernel
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

theorem integral_kernel (ω A B : ℝ) (hω : ω ≠ 0) :
    (∫ t in A..B, exponentialKernel ω t) =
      (exponentialKernel ω B - exponentialKernel ω A) /
        (Complex.I * (ω : ℂ)) := by
  exact integral_exp_mul_complex (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hω))

theorem norm_integral_kernel_le (ω A B : ℝ) (hω : ω ≠ 0) :
    ‖∫ t in A..B, exponentialKernel ω t‖ ≤ 2 / |ω| := by
  rw [integral_kernel ω A B hω, norm_div]
  have hnum : ‖exponentialKernel ω B - exponentialKernel ω A‖ ≤ 2 := by
    simpa only [norm_kernel, one_add_one_eq_two] using
      norm_sub_le (exponentialKernel ω B) (exponentialKernel ω A)
  simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] using
    div_le_div_of_nonneg_right hnum (norm_nonneg (Complex.I * (ω : ℂ)))

theorem continuous_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ξ : ι → ℝ) :
    Continuous (exponentialSum s a ξ) := by
  unfold exponentialSum
  exact continuous_finsetSum s (fun n _ => continuous_const.mul (continuous_kernel _))

theorem norm_square_expansion {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) (t : ℝ) :
    ((‖exponentialSum s a ξ t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, a m * conj (a n) * exponentialKernel (ξ m - ξ n) t := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [exponentialSum, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [← kernel_mul_conj]
  ring

theorem mean_square_expansion {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) (A B : ℝ) :
    ((∫ t in A..B, ‖exponentialSum s a ξ t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, a m * conj (a n) *
        ∫ t in A..B, exponentialKernel (ξ m - ξ n) t := by
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [norm_square_expansion]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [intervalIntegral.integral_finsetSum]
    · simp only [intervalIntegral.integral_const_mul]
    · intro n hn
      exact (continuous_const.mul (continuous_kernel _)).intervalIntegrable _ _
  · intro m hm
    exact (continuous_finsetSum s fun n _ =>
      continuous_const.mul (continuous_kernel _)).intervalIntegrable _ _

theorem mean_square_diagonal {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) (A B : ℝ) :
    ((∫ t in A..B, ‖exponentialSum s a ξ t‖ ^ 2 : ℝ) : ℂ) -
        ((B - A) * ∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) =
      ∑ m ∈ s, ∑ n ∈ s.erase m, a m * conj (a n) *
        ∫ t in A..B, exponentialKernel (ξ m - ξ n) t := by
  rw [mean_square_expansion]
  have hsplit :
      (∑ m ∈ s, ∑ n ∈ s, a m * conj (a n) *
        ∫ t in A..B, exponentialKernel (ξ m - ξ n) t) =
      ((B - A) * ∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) +
        ∑ m ∈ s, ∑ n ∈ s.erase m, a m * conj (a n) *
          ∫ t in A..B, exponentialKernel (ξ m - ξ n) t := by
    rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← Finset.add_sum_erase s
      (fun n => a m * conj (a n) * ∫ t in A..B, exponentialKernel (ξ m - ξ n) t) hm]
    congr 1
    simp [kernel_zero, Complex.mul_conj', Complex.real_smul, mul_comm]
  rw [hsplit]
  ring

theorem mean_square_error_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) (A B : ℝ)
    (hξ : Set.InjOn ξ (s : Set ι)) :
    |(∫ t in A..B, ‖exponentialSum s a ξ t‖ ^ 2) -
      (B - A) * ∑ n ∈ s, ‖a n‖ ^ 2| ≤
      ∑ m ∈ s, ∑ n ∈ s.erase m, 2 * ‖a m‖ * ‖a n‖ / |ξ m - ξ n| := by
  have hdiag := mean_square_diagonal s a ξ A B
  have hnorm := congrArg norm hdiag
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hnorm
  rw [hnorm]
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro m hm
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro n hn
  have hnm := Finset.mem_erase.mp hn
  have hne : ξ m - ξ n ≠ 0 := sub_ne_zero.mpr fun h =>
    hnm.1 (hξ hnm.2 hm h.symm)
  have hbound := mul_le_mul_of_nonneg_left (norm_integral_kernel_le (ξ m - ξ n) A B hne)
    (mul_nonneg (norm_nonneg (a m)) (norm_nonneg (a n)))
  simp only [norm_mul, RCLike.norm_conj]
  calc
    _ ≤ ‖a m‖ * ‖a n‖ * (2 / |ξ m - ξ n|) := hbound
    _ = _ := by ring

end Erdos374.PairSpacingKernel
end

#print axioms Erdos374.PairSpacingKernel.mean_square_error_le

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.PairSpacingKernel.exponentialKernel,
    ``Erdos374.PairSpacingKernel.exponentialSum,
    ``Erdos374.PairSpacingKernel.continuous_kernel,
    ``Erdos374.PairSpacingKernel.norm_kernel,
    ``Erdos374.PairSpacingKernel.kernel_zero,
    ``Erdos374.PairSpacingKernel.kernel_mul_conj,
    ``Erdos374.PairSpacingKernel.integral_kernel,
    ``Erdos374.PairSpacingKernel.norm_integral_kernel_le,
    ``Erdos374.PairSpacingKernel.continuous_sum,
    ``Erdos374.PairSpacingKernel.norm_square_expansion,
    ``Erdos374.PairSpacingKernel.mean_square_expansion,
    ``Erdos374.PairSpacingKernel.mean_square_diagonal,
    ``Erdos374.PairSpacingKernel.mean_square_error_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#eval "HARMAN ANALYTIC : finite mean-square expansion and kernel bounds checked"


