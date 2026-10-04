import FourPrimeGroupingCoefficients
import FactoredDivisorWeights

/-! Exact regrouping of a four-prime remainder. The first three prime
coordinates and the small divisor are collected by product, retaining all
representations; the last prime is the right factor. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace FourPrimeGrouping

def lastCoefficient (S4 : Finset ℕ) (n : ℕ) : ℝ := if n ∈ S4 then 1 else 0

theorem lastCoefficient_eq_one (S4 : Finset ℕ) (n : ℕ) (hn : n ∈ S4) :
    lastCoefficient S4 n = 1 := by simp [lastCoefficient, hn]

theorem lastCoefficient_abs_le_one (S4 : Finset ℕ) (n : ℕ) :
    |lastCoefficient S4 n| ≤ 1 := by
  by_cases hn : n ∈ S4 <;> simp [lastCoefficient, hn]

def fullSupport (S0 S1 S2 S3 S4 : Finset ℕ) : Finset ℕ :=
  FactoredDivisorWeights.support (support S0 S1 S2 S3) S4

def fullCoefficient (S0 S1 S2 S3 S4 : Finset ℕ) (C : ℕ → ℝ) : ℕ → ℝ :=
  FactoredDivisorWeights.coefficient (support S0 S1 S2 S3) S4
    (coefficient S0 S1 S2 S3 C) (lastCoefficient S4)

theorem fullSupport_positive (S0 S1 S2 S3 S4 : Finset ℕ)
    (h0 : ∀ n ∈ S0, 0 < n) (h1 : ∀ n ∈ S1, 0 < n)
    (h2 : ∀ n ∈ S2, 0 < n) (h3 : ∀ n ∈ S3, 0 < n)
    (h4 : ∀ n ∈ S4, 0 < n) (d : ℕ) (hd : d ∈ fullSupport S0 S1 S2 S3 S4) :
    0 < d := by
  exact HarmanDivisorWindow.productSupport_positive (support S0 S1 S2 S3) S4
    (support_positive S0 S1 S2 S3 h0 h1 h2 h3) h4 d hd

/-- Equality against every real kernel is the exact grouping statement;
no chosen representation or discarded repeated-prime tuple is used. -/
theorem grouped_kernel (S0 S1 S2 S3 S4 : Finset ℕ) (C kernel : ℕ → ℝ) :
    (∑ d ∈ fullSupport S0 S1 S2 S3 S4,
      fullCoefficient S0 S1 S2 S3 S4 C d * kernel d) =
      ∑ ν ∈ S0, ∑ p1 ∈ S1, ∑ p2 ∈ S2, ∑ p3 ∈ S3, ∑ p4 ∈ S4,
        C ν * kernel (ν * p1 * p2 * p3 * p4) := by
  change (∑ d ∈ FactoredDivisorWeights.support (support S0 S1 S2 S3) S4,
      FactoredDivisorWeights.coefficient (support S0 S1 S2 S3) S4
        (coefficient S0 S1 S2 S3 C) (lastCoefficient S4) d * kernel d) = _
  unfold FactoredDivisorWeights.support
  rw [FactoredDivisorWeights.grouped_sum _ _ _ _ _ _
    (HarmanDivisorWindow.productSupport_contains _ _), Finset.sum_product]
  calc
    _ = ∑ m ∈ support S0 S1 S2 S3,
        coefficient S0 S1 S2 S3 C m * (∑ n ∈ S4, kernel (m * n)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [lastCoefficient_eq_one S4 n hn, mul_one,
        DirichletProductCoefficients.productIndex]
    _ = ∑ ν ∈ S0, ∑ p1 ∈ S1, ∑ p2 ∈ S2, ∑ p3 ∈ S3,
        C ν * (∑ p4 ∈ S4, kernel (ν * p1 * p2 * p3 * p4)) :=
      grouped_sum_support S0 S1 S2 S3 C (fun m => ∑ n ∈ S4, kernel (m * n))
    _ = _ := by simp only [Finset.mul_sum]

theorem grouped_remainder (S0 S1 S2 S3 S4 : Finset ℕ) (C : ℕ → ℝ) (L R : ℝ) :
    HarmanDivisorWindow.remainder (fullSupport S0 S1 S2 S3 S4)
      (fullCoefficient S0 S1 S2 S3 S4 C) L R =
      ∑ ν ∈ S0, ∑ p1 ∈ S1, ∑ p2 ∈ S2, ∑ p3 ∈ S3, ∑ p4 ∈ S4,
        C ν * ((⌊R / ((ν * p1 * p2 * p3 * p4 : ℕ) : ℝ)⌋₊ : ℝ) -
          (⌊L / ((ν * p1 * p2 * p3 * p4 : ℕ) : ℝ)⌋₊ : ℝ) -
          (R - L) / ((ν * p1 * p2 * p3 * p4 : ℕ) : ℝ)) := by
  rw [HarmanDivisorWindow.remainder_eq_sum]
  exact grouped_kernel S0 S1 S2 S3 S4 C
    (fun d => (⌊R / d⌋₊ : ℝ) - (⌊L / d⌋₊ : ℝ) - (R - L) / d)

/-- The actual variable window is retained exactly, including its factor Y/X. -/
theorem grouped_window_remainder (S0 S1 S2 S3 S4 : Finset ℕ)
    (C : ℕ → ℝ) (X Y x : ℝ) :
    HarmanDivisorWindow.remainder (fullSupport S0 S1 S2 S3 S4)
      (fullCoefficient S0 S1 S2 S3 S4 C) (x - x * (Y / X)) x =
      ∑ ν ∈ S0, ∑ p1 ∈ S1, ∑ p2 ∈ S2, ∑ p3 ∈ S3, ∑ p4 ∈ S4,
        C ν * ((⌊x / ((ν * p1 * p2 * p3 * p4 : ℕ) : ℝ)⌋₊ : ℝ) -
          (⌊(x - x * (Y / X)) / ((ν * p1 * p2 * p3 * p4 : ℕ) : ℝ)⌋₊ : ℝ) -
          (x * (Y / X)) / ((ν * p1 * p2 * p3 * p4 : ℕ) : ℝ)) := by
  simpa only [show x - (x - x * (Y / X)) = x * (Y / X) by ring] using
    grouped_remainder S0 S1 S2 S3 S4 C (x - x * (Y / X)) x

#print axioms grouped_kernel
#print axioms grouped_window_remainder
run_cmd do
  for decl in [``lastCoefficient_eq_one, ``lastCoefficient_abs_le_one,
      ``fullSupport_positive, ``grouped_kernel, ``grouped_remainder,
      ``grouped_window_remainder] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end FourPrimeGrouping
end
