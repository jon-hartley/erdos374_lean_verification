import DirichletPowerCoefficients

/-!
The coefficient construction is the exact power expansion of the
logarithmic exponential polynomial, with no surrogate frequencies.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace DirichletPowerExpansion
open DirichletPowerCoefficients Erdos374.HarmanAnalytic151MeanSquare

theorem kernel_product (k : ℕ) (f : Fin k → ℕ) (hf : ∀ i, 0 < f i) (t : ℝ) :
    exponentialKernel151 (Real.log (productIndex f)) t =
      ∏ i, exponentialKernel151 (Real.log (f i)) t := by
  have hlog : Real.log (productIndex f) = ∑ i, Real.log (f i) := by
    unfold productIndex
    rw [Nat.cast_prod]
    exact Real.log_prod (fun i _ => by exact_mod_cast (hf i).ne')
  unfold exponentialKernel151
  rw [hlog, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul, Complex.exp_sum]

theorem exponential_power (s target : Finset ℕ) (k : ℕ) (coeff : ℕ → ℂ) (t : ℝ)
    (hs : ∀ n ∈ s, 0 < n)
    (hmap : ∀ f ∈ tuples s k, productIndex f ∈ target) :
    exponentialSum151 s coeff (fun n => Real.log n) t ^ k =
      exponentialSum151 target (coefficient s k coeff) (fun n => Real.log n) t := by
  unfold exponentialSum151
  rw [grouped_sum s target k coeff (fun n => exponentialKernel151 (Real.log n) t) hmap,
    Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro f hf
  rw [Finset.prod_mul_distrib, ← kernel_product k f
    (fun i => hs (f i) (Fintype.mem_piFinset.mp hf i)) t]
  rfl

theorem norm_power (s : Finset ℕ) (k L : ℕ) (coeff : ℕ → ℂ) (t : ℝ)
    (hs : ∀ n ∈ s, 0 < n ∧ n ≤ L) :
    ‖exponentialSum151 s coeff (fun n => Real.log n) t‖ ^ (2 * k) =
      ‖exponentialSum151 (Finset.Icc 1 (L ^ k)) (coefficient s k coeff)
        (fun n => Real.log n) t‖ ^ 2 := by
  have hmap : ∀ f ∈ tuples s k, productIndex f ∈ Finset.Icc 1 (L ^ k) := by
    intro f hf
    exact Finset.mem_Icc.mpr ⟨product_positive s k (fun n hn => (hs n hn).1) f hf,
      product_le s k L (fun n hn => (hs n hn).2) f hf⟩
  rw [← exponential_power s _ k coeff t (fun n hn => (hs n hn).1) hmap, norm_pow,
    ← pow_mul, Nat.mul_comm]

end DirichletPowerExpansion

#print axioms DirichletPowerExpansion.norm_power
run_cmd do
  let axioms ← Lean.collectAxioms ``DirichletPowerExpansion.norm_power
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "DIRICHLET POWER EXPANSION PASSED"
