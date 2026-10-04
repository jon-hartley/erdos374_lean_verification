import DirichletProductCoefficients

/-!
The mixed coefficients represent the actual product of logarithmic
exponential sums. The normalization below preserves the full product,
so later large-value estimates do not assume a cap for individual blocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace DirichletProductExpansion
open DirichletProductCoefficients Erdos374.HarmanAnalytic151MeanSquare
open Erdos374.HarmanGram152

theorem kernel_product (left right : ℕ) (hl : 0 < left) (hr : 0 < right)
    (t : ℝ) :
    exponentialKernel151 (Real.log (left * right : ℕ)) t =
      exponentialKernel151 (Real.log left) t *
        exponentialKernel151 (Real.log right) t := by
  have hlr : (left : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have hrr : (right : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Nat.cast_mul, Real.log_mul hlr hrr]
  simp only [exponentialKernel151, Complex.ofReal_add, mul_add, add_mul,
    Complex.exp_add]

theorem exponential_product (leftSupport rightSupport target : Finset ℕ)
    (left right : ℕ → ℂ) (t : ℝ)
    (hleft : ∀ n ∈ leftSupport, 0 < n)
    (hright : ∀ n ∈ rightSupport, 0 < n)
    (hmap : ∀ pair ∈ leftSupport ×ˢ rightSupport, productIndex pair ∈ target) :
    exponentialSum151 leftSupport left (fun n => Real.log n) t *
      exponentialSum151 rightSupport right (fun n => Real.log n) t =
        exponentialSum151 target (coefficient leftSupport rightSupport left right)
          (fun n => Real.log n) t := by
  unfold exponentialSum151
  rw [grouped_sum leftSupport rightSupport target left right
    (fun n => exponentialKernel151 (Real.log n) t) hmap,
    Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro leftIndex hl
  apply Finset.sum_congr rfl
  intro rightIndex hr
  dsimp [pairWeight, productIndex]
  rw [kernel_product leftIndex rightIndex (hleft leftIndex hl)
    (hright rightIndex hr) t]
  ring

theorem normalized_product_norm (leftSupport rightSupport target : Finset ℕ)
    (left right : ℕ → ℂ) (σ t : ℝ)
    (hleft : ∀ n ∈ leftSupport, 0 < n)
    (hright : ∀ n ∈ rightSupport, 0 < n)
    (hmap : ∀ pair ∈ leftSupport ×ˢ rightSupport, productIndex pair ∈ target) :
    ‖verticalDirichlet152 leftSupport left σ t *
      verticalDirichlet152 rightSupport right σ t‖ =
        ‖exponentialSum151 target
          (coefficient leftSupport rightSupport
            (fun n => conj (normalizedCoefficients152 left σ n))
            (fun n => conj (normalizedCoefficients152 right σ n)))
          (fun n => Real.log n) t‖ := by
  rw [norm_mul, verticalDirichlet_norm152 leftSupport left σ t hleft,
    verticalDirichlet_norm152 rightSupport right σ t hright, ← norm_mul,
    exponential_product leftSupport rightSupport target _ _ t hleft hright hmap]

end DirichletProductExpansion

#print axioms DirichletProductExpansion.normalized_product_norm
run_cmd do
  let axioms ← Lean.collectAxioms ``DirichletProductExpansion.normalized_product_norm
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "DIRICHLET PRODUCT EXPANSION PASSED"
