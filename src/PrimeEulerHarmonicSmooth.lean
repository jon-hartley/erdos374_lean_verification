import SieveEulerRatio
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Finite harmonic comparison with the actual strict prime Euler product.
Only geometric summability along each prime power is used. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace PrimeEulerHarmonicSmooth
open SieveStoppingExpansion

def smoothBelow (z : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => n ∈ Nat.factoredNumbers (SieveSmallWeights.pool z))

def excludedPrimes (z : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun p => p.Prime ∧ z ≤ (p:ℝ))

theorem reciprocal_prime_power_hasSum (p : ℕ) (hp : p.Prime) :
    HasSum (fun n : ℕ => ((p^n : ℕ):ℝ)⁻¹) (1-(p:ℝ)⁻¹)⁻¹ := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hi0 : (0:ℝ) ≤ (p:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hi1 : (p:ℝ)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hp1
  simpa only [Nat.cast_pow, inv_pow] using hasSum_geometric_of_lt_one hi0 hi1

theorem reciprocal_factored_hasSum (z : ℝ) :
    HasSum (fun n : Nat.factoredNumbers (SieveSmallWeights.pool z) => (n.val:ℝ)⁻¹)
      (primeEuler z)⁻¹ := by
  have hh := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (n:ℝ)⁻¹) (by norm_num)
    (by intro m n _; simp only [Nat.cast_mul, mul_inv_rev]; ring)
    (by
      intro p hp
      have he : (fun n : ℕ => ‖((p^n:ℕ):ℝ)⁻¹‖) =
          (fun n : ℕ => ((p^n:ℕ):ℝ)⁻¹) := by
        funext n
        exact Real.norm_of_nonneg (by positivity)
      rw [he]
      exact (reciprocal_prime_power_hasSum p hp).summable)
    (SieveSmallWeights.pool z)
  convert hh.2 using 1
  simp only [primeEuler, SievePrefixLoss.euler, SieveSmallWeights.primes_toFinset]
  rw [← Finset.prod_inv_distrib]
  rw [Finset.filter_true_of_mem (fun p hp => ((SieveSmallWeights.mem_pool z p).mp hp).1)]
  apply Finset.prod_congr rfl
  intro p hp
  exact (reciprocal_prime_power_hasSum p ((SieveSmallWeights.mem_pool z p).mp hp).1).tsum_eq.symm

theorem smooth_sum_le_inverse (z : ℝ) (N : ℕ) :
    (∑ n ∈ smoothBelow z N, (n:ℝ)⁻¹) ≤ (primeEuler z)⁻¹ := by
  let S : Finset (Nat.factoredNumbers (SieveSmallWeights.pool z)) :=
    (smoothBelow z N).attach.map
      ⟨fun n => ⟨n.val, (Finset.mem_filter.mp n.property).2⟩,
        by
          intro a b h
          apply Subtype.ext
          exact congrArg (fun v : Nat.factoredNumbers (SieveSmallWeights.pool z) => v.val) h⟩
  have hh := sum_le_hasSum S
    (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n.val)) (reciprocal_factored_hasSum z)
  dsimp only [S] at hh
  rw [Finset.sum_map] at hh
  change (∑ n ∈ (smoothBelow z N).attach, (n.val:ℝ)⁻¹) ≤ (primeEuler z)⁻¹ at hh
  rw [Finset.sum_attach (smoothBelow z N) (fun n : ℕ => (n:ℝ)⁻¹)] at hh
  exact hh

run_cmd do
  for decl in [``reciprocal_prime_power_hasSum, ``reciprocal_factored_hasSum,
      ``smooth_sum_le_inverse] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FINITE SMOOTH HARMONIC MASS BELOW THE ACTUAL EULER INVERSE"

end PrimeEulerHarmonicSmooth
end
