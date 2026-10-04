import FourPrimePartitionProduct
import FactoredDivisorWeights
import FiniteDivisorFamily

/-! The finite partition preserves the actual convolution-weighted divisor
remainder at arbitrary endpoints. Product collisions remain summed. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace FourPrimePartition

def productBlockSupport (S T : Finset ℕ) (a b : ℕ) (ij : ℕ × ℕ) : Finset ℕ :=
  FactoredDivisorWeights.support (block S a ij.1) (block T b ij.2)

def productBlockCoefficient (S T : Finset ℕ) (a b : ℕ)
    (left right : ℕ → ℝ) (ij : ℕ × ℕ) : ℕ → ℝ :=
  FactoredDivisorWeights.coefficient (block S a ij.1) (block T b ij.2) left right

/-- Equality for every kernel retains all coefficients and product collisions. -/
theorem partition_kernel (S T : Finset ℕ) (a b k l : ℕ)
    (left right kernel : ℕ → ℝ)
    (hS : ∀ n ∈ S, a < n ∧ n ≤ scale a (k+1))
    (hT : ∀ n ∈ T, b < n ∧ n ≤ scale b (l+1)) :
    (∑ d ∈ FiniteDivisorFamily.support (family S T a b k l)
        (productBlockSupport S T a b),
      FiniteDivisorFamily.coefficient (family S T a b k l)
        (productBlockSupport S T a b)
        (productBlockCoefficient S T a b left right) d * kernel d) =
      ∑ d ∈ FactoredDivisorWeights.support S T,
        FactoredDivisorWeights.coefficient S T left right d * kernel d := by
  rw [FiniteDivisorFamily.sum_coefficient]
  calc
    _ = ∑ ij ∈ family S T a b k l,
        ∑ m ∈ block S a ij.1, ∑ n ∈ block T b ij.2,
          (left m*right n)*kernel (m*n) := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hh := FactoredDivisorWeights.grouped_sum (block S a ij.1) (block T b ij.2)
        (FactoredDivisorWeights.support (block S a ij.1) (block T b ij.2))
        left right kernel (HarmanDivisorWindow.productSupport_contains _ _)
      simpa only [productBlockSupport, productBlockCoefficient, Finset.sum_product,
        DirichletProductCoefficients.productIndex] using hh
    _ = ∑ m ∈ S, ∑ n ∈ T, (left m*right n)*kernel (m*n) :=
      sum_family_blocks S T a b k l (fun m n => (left m*right n)*kernel (m*n)) hS hT
    _ = _ := by
      have hh := FactoredDivisorWeights.grouped_sum S T (FactoredDivisorWeights.support S T)
        left right kernel (HarmanDivisorWindow.productSupport_contains _ _)
      simpa only [Finset.sum_product, DirichletProductCoefficients.productIndex] using hh.symm

theorem partition_remainder (S T : Finset ℕ) (a b k l : ℕ)
    (left right : ℕ → ℝ) (L R : ℝ)
    (hS : ∀ n ∈ S, a < n ∧ n ≤ scale a (k+1))
    (hT : ∀ n ∈ T, b < n ∧ n ≤ scale b (l+1)) :
    HarmanDivisorWindow.remainder
      (FiniteDivisorFamily.support (family S T a b k l) (productBlockSupport S T a b))
      (FiniteDivisorFamily.coefficient (family S T a b k l)
        (productBlockSupport S T a b) (productBlockCoefficient S T a b left right)) L R =
      HarmanDivisorWindow.remainder (FactoredDivisorWeights.support S T)
        (FactoredDivisorWeights.coefficient S T left right) L R := by
  simp only [HarmanDivisorWindow.remainder_eq_sum]
  exact partition_kernel S T a b k l left right
    (fun d => (⌊R/(d:ℝ)⌋₊:ℝ)-(⌊L/(d:ℝ)⌋₊:ℝ)-(R-L)/(d:ℝ)) hS hT

theorem partition_remainder_eq_sum (S T : Finset ℕ) (a b k l : ℕ)
    (left right : ℕ → ℝ) (L R : ℝ)
    (hS : ∀ n ∈ S, a < n ∧ n ≤ scale a (k+1))
    (hT : ∀ n ∈ T, b < n ∧ n ≤ scale b (l+1)) :
    HarmanDivisorWindow.remainder (FactoredDivisorWeights.support S T)
        (FactoredDivisorWeights.coefficient S T left right) L R =
      ∑ ij ∈ family S T a b k l,
        HarmanDivisorWindow.remainder (productBlockSupport S T a b ij)
          (productBlockCoefficient S T a b left right ij) L R := by
  rw [← partition_remainder S T a b k l left right L R hS hT]
  exact FiniteDivisorFamily.remainder_eq_sum _ _ _ L R

/-- Argument order suitable for rewriting inside a variable-window integral. -/
theorem remainder_family_eq (S T : Finset ℕ) (a b k l : ℕ)
    (left right : ℕ → ℝ)
    (hS : ∀ n ∈ S, a < n ∧ n ≤ scale a (k+1))
    (hT : ∀ n ∈ T, b < n ∧ n ≤ scale b (l+1)) (L R : ℝ) :
    HarmanDivisorWindow.remainder
      (FiniteDivisorFamily.support (family S T a b k l)
        (fun ij => FactoredDivisorWeights.support (block S a ij.1) (block T b ij.2)))
      (FiniteDivisorFamily.coefficient (family S T a b k l)
        (fun ij => FactoredDivisorWeights.support (block S a ij.1) (block T b ij.2))
        (fun ij => FactoredDivisorWeights.coefficient
          (block S a ij.1) (block T b ij.2) left right)) L R =
      HarmanDivisorWindow.remainder (FactoredDivisorWeights.support S T)
        (FactoredDivisorWeights.coefficient S T left right) L R :=
  partition_remainder S T a b k l left right L R hS hT

#print axioms partition_kernel
#print axioms partition_remainder
run_cmd do
  for target in [``partition_kernel, ``partition_remainder, ``partition_remainder_eq_sum,
      ``remainder_family_eq] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "FOUR_PRIME_PARTITION_REMAINDER_PASSED"

end FourPrimePartition
end
