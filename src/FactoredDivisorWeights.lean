import HarmanDivisorWindow
import ProductCoefficientCap

/-!
Real signed coefficients for the full convolution of two finite divisor
families. Every representation is retained in the actual image support.
Polynomial and reciprocal-mass factorizations are exact identities.
The eventual coefficient cap requires bounded factor weights and an
explicit product-index bound; no sieve identification is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter
open scoped BigOperators

namespace FactoredDivisorWeights
open Erdos374.HarmanGram152

def support (leftSupport rightSupport : Finset ℕ) : Finset ℕ :=
  HarmanDivisorWindow.productSupport leftSupport rightSupport

def coefficient (leftSupport rightSupport : Finset ℕ)
    (left right : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ pair ∈ (leftSupport ×ˢ rightSupport).filter
    (fun pair => DirichletProductCoefficients.productIndex pair = n),
      left pair.1 * right pair.2

theorem coefficient_cast (leftSupport rightSupport : Finset ℕ)
    (left right : ℕ → ℝ) (n : ℕ) :
    (coefficient leftSupport rightSupport left right n : ℂ) =
      DirichletProductCoefficients.coefficient leftSupport rightSupport
        (fun n => (left n : ℂ)) (fun n => (right n : ℂ)) n := by
  simp [coefficient, DirichletProductCoefficients.coefficient,
    DirichletProductCoefficients.pairWeight, Complex.ofReal_sum]

theorem grouped_sum (leftSupport rightSupport target : Finset ℕ)
    (left right kernel : ℕ → ℝ)
    (hmap : ∀ pair ∈ leftSupport ×ˢ rightSupport,
      DirichletProductCoefficients.productIndex pair ∈ target) :
    (∑ n ∈ target, coefficient leftSupport rightSupport left right n * kernel n) =
      ∑ pair ∈ leftSupport ×ˢ rightSupport,
        (left pair.1 * right pair.2) *
          kernel (DirichletProductCoefficients.productIndex pair) := by
  apply Complex.ofReal_injective
  have hh := DirichletProductCoefficients.grouped_sum leftSupport rightSupport target
    (fun n => (left n : ℂ)) (fun n => (right n : ℂ))
    (fun n => (kernel n : ℂ)) hmap
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, coefficient_cast,
    DirichletProductCoefficients.pairWeight] using hh

theorem vertical_product (leftSupport rightSupport target : Finset ℕ)
    (left right : ℕ → ℝ) (σ t : ℝ)
    (hmap : ∀ pair ∈ leftSupport ×ˢ rightSupport,
      DirichletProductCoefficients.productIndex pair ∈ target) :
    verticalDirichlet152 target
      (fun n => (coefficient leftSupport rightSupport left right n : ℂ)) σ t =
      verticalDirichlet152 leftSupport (fun n => (left n : ℂ)) σ t *
        verticalDirichlet152 rightSupport (fun n => (right n : ℂ)) σ t := by
  unfold verticalDirichlet152
  simp_rw [coefficient_cast]
  rw [DirichletProductCoefficients.grouped_sum leftSupport rightSupport target
    (fun n => (left n : ℂ)) (fun n => (right n : ℂ))
    (fun n => (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)))) hmap,
    Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  simp only [DirichletProductCoefficients.pairWeight,
    DirichletProductCoefficients.productIndex, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  ring

theorem vertical_product_support (leftSupport rightSupport : Finset ℕ)
    (left right : ℕ → ℝ) (σ t : ℝ) :
    verticalDirichlet152 (support leftSupport rightSupport)
      (fun n => (coefficient leftSupport rightSupport left right n : ℂ)) σ t =
      verticalDirichlet152 leftSupport (fun n => (left n : ℂ)) σ t *
        verticalDirichlet152 rightSupport (fun n => (right n : ℂ)) σ t :=
  vertical_product leftSupport rightSupport _ left right σ t
    (HarmanDivisorWindow.productSupport_contains _ _)

theorem support_bounds (M N : ℕ) (leftSupport rightSupport : Finset ℕ)
    (hN : 1 ≤ N)
    (hleft : ∀ n ∈ leftSupport, M < n ∧ n ≤ 2 * M)
    (hright : ∀ n ∈ rightSupport, N < n ∧ n ≤ 2 * N)
    (d : ℕ) (hd : d ∈ support leftSupport rightSupport) :
    M * N < d ∧ d ≤ 4 * M * N := by
  obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp hd
  exact Finset.mem_Ioc.mp
    (DirichletProductCoefficients.product_support M N hN
      leftSupport rightSupport hleft hright pair hp)

theorem support_fourfold (M N : ℕ) (leftSupport rightSupport : Finset ℕ)
    (hN : 1 ≤ N)
    (hleft : ∀ n ∈ leftSupport, M < n ∧ n ≤ 2 * M)
    (hright : ∀ n ∈ rightSupport, N < n ∧ n ≤ 2 * N)
    (d : ℕ) (hd : d ∈ support leftSupport rightSupport) :
    ((M * N : ℕ) : ℝ) < d ∧ (d : ℝ) ≤ 4 * ((M * N : ℕ) : ℝ) := by
  have hh := support_bounds M N leftSupport rightSupport hN hleft hright d hd
  constructor
  · exact_mod_cast hh.1
  · have hu : d ≤ 4 * (M * N) := by simpa only [mul_assoc] using hh.2
    exact_mod_cast hu

theorem reciprocal_mass (leftSupport rightSupport : Finset ℕ)
    (left right : ℕ → ℝ) :
    HarmanDivisorWindow.reciprocalMass (support leftSupport rightSupport)
      (coefficient leftSupport rightSupport left right) =
      HarmanDivisorWindow.reciprocalMass leftSupport left *
        HarmanDivisorWindow.reciprocalMass rightSupport right := by
  unfold HarmanDivisorWindow.reciprocalMass
  have hh := grouped_sum leftSupport rightSupport (support leftSupport rightSupport)
    left right (fun n => (n : ℝ)⁻¹)
    (HarmanDivisorWindow.productSupport_contains _ _)
  calc
    _ = ∑ pair ∈ leftSupport ×ˢ rightSupport,
        (left pair.1 * right pair.2) /
          (DirichletProductCoefficients.productIndex pair : ℝ) := by
      simpa only [div_eq_mul_inv] using hh
    _ = _ := by
      rw [Finset.sum_mul_sum, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      simp only [DirichletProductCoefficients.productIndex, Nat.cast_mul,
        div_eq_mul_inv, mul_inv_rev]
      ring

theorem eventual_pointwise_cap (β : ℝ) (hβ : 0 < β) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (leftSupport rightSupport : Finset ℕ) (left right : ℕ → ℝ) (d : ℕ),
        0 < d → (d : ℝ) ≤ X ^ (2 : ℕ) →
        (∀ n ∈ leftSupport, |left n| ≤ 1) →
        (∀ n ∈ rightSupport, |right n| ≤ 1) →
        |coefficient leftSupport rightSupport left right d| ≤ X ^ β := by
  filter_upwards [ProductCoefficientCap.eventually_bound β hβ] with X hh
  refine ⟨hh.1, ?_⟩
  intro leftSupport rightSupport left right d hd hdX hleft hright
  have hone : (1 : ℝ) ≤ X ^ (β / 8) := Real.one_le_rpow hh.1 (by positivity)
  have hc := hh.2 leftSupport rightSupport
    (fun n => (left n : ℂ)) (fun n => (right n : ℂ)) d hd hdX
    (fun n hn => by simpa only [Complex.norm_real, Real.norm_eq_abs]
      using (hleft n hn).trans hone)
    (fun n hn => by simpa only [Complex.norm_real, Real.norm_eq_abs]
      using (hright n hn).trans hone)
  rw [← coefficient_cast] at hc
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hc

theorem eventual_support_cap (β : ℝ) (hβ : 0 < β) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (M N : ℕ) (leftSupport rightSupport : Finset ℕ) (left right : ℕ → ℝ),
        1 ≤ N → ((4 * M * N : ℕ) : ℝ) ≤ X ^ (2 : ℕ) →
        (∀ n ∈ leftSupport, M < n ∧ n ≤ 2 * M) →
        (∀ n ∈ rightSupport, N < n ∧ n ≤ 2 * N) →
        (∀ n ∈ leftSupport, |left n| ≤ 1) →
        (∀ n ∈ rightSupport, |right n| ≤ 1) →
        ∀ d ∈ support leftSupport rightSupport,
          |coefficient leftSupport rightSupport left right d| ≤ X ^ β := by
  filter_upwards [eventual_pointwise_cap β hβ] with X hh
  refine ⟨hh.1, ?_⟩
  intro M N leftSupport rightSupport left right hN hscale hleft hright ham han d hd
  have hb := support_bounds M N leftSupport rightSupport hN hleft hright d hd
  have hdp : 0 < d := by omega
  have hdX : (d : ℝ) ≤ X ^ (2 : ℕ) :=
    (by exact_mod_cast hb.2 : (d : ℝ) ≤ (4 * M * N : ℕ)).trans hscale
  exact hh.2 leftSupport rightSupport left right d hdp hdX ham han

end FactoredDivisorWeights

#print axioms FactoredDivisorWeights.vertical_product_support
#print axioms FactoredDivisorWeights.reciprocal_mass
run_cmd do
  for target in [``FactoredDivisorWeights.coefficient_cast,
      ``FactoredDivisorWeights.grouped_sum,
      ``FactoredDivisorWeights.vertical_product,
      ``FactoredDivisorWeights.vertical_product_support,
      ``FactoredDivisorWeights.support_bounds,
      ``FactoredDivisorWeights.support_fourfold,
      ``FactoredDivisorWeights.reciprocal_mass,
      ``FactoredDivisorWeights.eventual_pointwise_cap,
      ``FactoredDivisorWeights.eventual_support_cap] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FACTORED DIVISOR WEIGHTS PASSED"
