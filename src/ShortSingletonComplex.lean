import ShortSingletonCollection
import FactoredDivisorScaling
import UpperAfter545Remaining

/-! Exact real/imaginary reduction for the original natural-floor discrepancy.
The two real products retain all physical product representations. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace ShortSingletonComplex
open UpperAfter545Remaining (floorKernel)

def productSum (A B : Finset ℕ) (a b : ℕ → ℂ) (L R : ℝ) : ℂ :=
  ∑ m ∈ A, ∑ n ∈ B, a m * b n * (floorKernel L R (m*n) : ℂ)

def realRemainder (A B : Finset ℕ) (a b : ℕ → ℝ) (L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder (FactoredDivisorWeights.support A B)
    (FactoredDivisorWeights.coefficient A B a b) L R

theorem realRemainder_eq_sum (A B : Finset ℕ) (a b : ℕ → ℝ) (L R : ℝ) :
    realRemainder A B a b L R =
      ∑ m ∈ A, ∑ n ∈ B, a m*b n*floorKernel L R (m*n) := by
  unfold realRemainder
  rw [HarmanDivisorWindow.remainder_eq_sum]
  change (∑ k ∈ FactoredDivisorWeights.support A B,
    FactoredDivisorWeights.coefficient A B a b k * floorKernel L R k) = _
  rw [FactoredDivisorWeights.grouped_sum A B (FactoredDivisorWeights.support A B)
    a b (floorKernel L R)
    (HarmanDivisorWindow.productSupport_contains A B), Finset.sum_product]
  rfl

theorem productSum_re (A B : Finset ℕ) (a b : ℕ → ℂ) (L R : ℝ) :
    (productSum A B a b L R).re =
      realRemainder A B (fun n => (a n).re) (fun n => (b n).re) L R -
      realRemainder A B (fun n => (a n).im) (fun n => (b n).im) L R := by
  simp only [productSum, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, realRemainder_eq_sum]
  simp_rw [sub_mul, Finset.sum_sub_distrib]

theorem productSum_im (A B : Finset ℕ) (a b : ℕ → ℂ) (L R : ℝ) :
    (productSum A B a b L R).im =
      realRemainder A B (fun n => (a n).re) (fun n => (b n).im) L R +
      realRemainder A B (fun n => (a n).im) (fun n => (b n).re) L R := by
  simp only [productSum, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_add, realRemainder_eq_sum]
  simp_rw [add_mul, Finset.sum_add_distrib]

theorem realRemainder_normalize_left (A B : Finset ℕ) (a b : ℕ → ℝ)
    (T L R : ℝ) (hT : T ≠ 0) :
    realRemainder A B a b L R =
      T * realRemainder A B (fun n => a n/T) b L R := by
  have ha : (fun n => T*(a n/T)) = a := by funext n; field_simp
  simpa only [realRemainder, ha, mul_one, one_mul] using
    FactoredDivisorScaling.factored_remainder_scale A B (fun n => a n/T) b T 1 L R

theorem normalized_parts_le_one (A : Finset ℕ) (a : ℕ → ℂ) (T : ℝ)
    (hT : 0 < T) (ha : ∀ n ∈ A, ‖a n‖ ≤ T) :
    (∀ n ∈ A, |(a n).re/T| ≤ 1) ∧ (∀ n ∈ A, |(a n).im/T| ≤ 1) := by
  constructor
  · intro n hn
    rw [abs_div, abs_of_pos hT]
    exact (div_le_one hT).mpr ((Complex.abs_re_le_norm (a n)).trans (ha n hn))
  · intro n hn
    rw [abs_div, abs_of_pos hT]
    exact (div_le_one hT).mpr ((Complex.abs_im_le_norm (a n)).trans (ha n hn))

run_cmd do
  for decl in [``realRemainder_eq_sum, ``productSum_re, ``productSum_im,
      ``realRemainder_normalize_left, ``normalized_parts_le_one] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "EXACT COMPLEX-TO-REAL FACTORED FLOOR REMAINDER PASSED"

end ShortSingletonComplex
