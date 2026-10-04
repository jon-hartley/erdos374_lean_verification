import DivisorPowerBound
import NormalizedMeanSquare

/-!
Exact coefficients obtained by grouping ordered products of indices.
Their squared energy is controlled by the multiplicity of each product.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace DirichletPowerCoefficients

def tuples (s : Finset ℕ) (k : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun _ : Fin k => s)

def productIndex {k : ℕ} (f : Fin k → ℕ) : ℕ := ∏ i, f i

def tupleWeight {k : ℕ} (coeff : ℕ → ℂ) (f : Fin k → ℕ) : ℂ :=
  ∏ i, coeff (f i)

def coefficient (s : Finset ℕ) (k : ℕ) (coeff : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ f ∈ (tuples s k).filter (fun f => productIndex f = n), tupleWeight coeff f

theorem product_positive (s : Finset ℕ) (k : ℕ)
    (hs : ∀ n ∈ s, 0 < n) (f : Fin k → ℕ) (hf : f ∈ tuples s k) :
    0 < productIndex f := by
  apply Finset.prod_pos
  intro i _
  exact hs (f i) (Fintype.mem_piFinset.mp hf i)

theorem product_le (s : Finset ℕ) (k L : ℕ)
    (hs : ∀ n ∈ s, n ≤ L) (f : Fin k → ℕ) (hf : f ∈ tuples s k) :
    productIndex f ≤ L ^ k := by
  calc
    _ ≤ ∏ _i : Fin k, L := Finset.prod_le_prod
      (fun i _ => hs (f i) (Fintype.mem_piFinset.mp hf i))
    _ = _ := by simp

theorem fiber_card_bound (s : Finset ℕ) (k n : ℕ) (hn : n ≠ 0) :
    ((tuples s k).filter (fun f => productIndex f = n)).card ≤
      n.divisors.card ^ k := by
  have hsub : (tuples s k).filter (fun f => productIndex f = n) ⊆
      Fintype.piFinset (fun _ : Fin k => n.divisors) := by
    intro f hf
    have heq := (Finset.mem_filter.mp hf).2
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hn⟩
    rw [← heq]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  simpa using Finset.card_le_card hsub

theorem tuple_energy (s : Finset ℕ) (k : ℕ) (coeff : ℕ → ℂ) :
    (∑ f ∈ tuples s k, ‖tupleWeight coeff f‖ ^ 2) =
      (∑ n ∈ s, ‖coeff n‖ ^ 2) ^ k := by
  simp only [tupleWeight, norm_prod, ← Finset.prod_pow]
  exact (Finset.sum_pow' s (fun n => ‖coeff n‖ ^ 2) k).symm

theorem grouped_sum (s t : Finset ℕ) (k : ℕ) (coeff kernel : ℕ → ℂ)
    (hmap : ∀ f ∈ tuples s k, productIndex f ∈ t) :
    (∑ n ∈ t, coefficient s k coeff n * kernel n) =
      ∑ f ∈ tuples s k, tupleWeight coeff f * kernel (productIndex f) := by
  unfold coefficient
  simp_rw [Finset.sum_mul]
  have hh := Finset.sum_fiberwise_of_maps_to hmap
    (fun f => tupleWeight coeff f * kernel (productIndex f))
  rw [← hh]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro f hf
  rw [(Finset.mem_filter.mp hf).2]

theorem energy_bound (s t : Finset ℕ) (k : ℕ) (coeff : ℕ → ℂ) (D : ℝ)
    (hmap : ∀ f ∈ tuples s k, productIndex f ∈ t)
    (hcard : ∀ n ∈ t,
      (((tuples s k).filter (fun f => productIndex f = n)).card : ℝ) ≤ D) :
    (∑ n ∈ t, ‖coefficient s k coeff n‖ ^ 2) ≤
      D * (∑ n ∈ s, ‖coeff n‖ ^ 2) ^ k := by
  calc
    _ ≤ ∑ n ∈ t, D * ∑ f ∈ (tuples s k).filter
        (fun f => productIndex f = n), ‖tupleWeight coeff f‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply (Erdos374.ExponentialSum151.norm_sum_sq_le_card_energy
        ((tuples s k).filter (fun f => productIndex f = n)) (tupleWeight coeff)).trans
      exact mul_le_mul_of_nonneg_right (hcard n hn)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = D * (∑ f ∈ tuples s k, ‖tupleWeight coeff f‖ ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hmap]
    _ = _ := by rw [tuple_energy]

end DirichletPowerCoefficients

#print axioms DirichletPowerCoefficients.energy_bound
run_cmd do
  for decl in [``DirichletPowerCoefficients.fiber_card_bound,
      ``DirichletPowerCoefficients.grouped_sum, ``DirichletPowerCoefficients.energy_bound] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "DIRICHLET POWER COEFFICIENTS PASSED"
