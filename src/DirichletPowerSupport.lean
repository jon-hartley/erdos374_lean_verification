import DirichletPowerEnergy
import DirichletPowerExpansion

/-!
Powers of a polynomial supported on (N,2N] have support on
(N^k,(2N)^k]. The strict lower endpoint is retained explicitly.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace DirichletPowerSupport
open DirichletPowerCoefficients Erdos374.HarmanAnalytic151MeanSquare

theorem product_gt (s : Finset ℕ) (N k : ℕ) (hk : 1 ≤ k)
    (hs : ∀ n ∈ s, N < n) (f : Fin k → ℕ) (hf : f ∈ tuples s k) :
    N ^ k < productIndex f := by
  have hh : (N + 1) ^ k ≤ productIndex f := by
    calc
      _ = ∏ _i : Fin k, (N + 1) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun i _ =>
        hs (f i) (Fintype.mem_piFinset.mp hf i))
  exact (Nat.pow_lt_pow_left (Nat.lt_succ_self N) (by omega : k ≠ 0)).trans_le hh

theorem product_mem (s : Finset ℕ) (N k : ℕ) (hk : 1 ≤ k)
    (hs : ∀ n ∈ s, N < n ∧ n ≤ 2 * N) (f : Fin k → ℕ) (hf : f ∈ tuples s k) :
    productIndex f ∈ Finset.Ioc (N ^ k) (2 ^ k * N ^ k) := by
  refine Finset.mem_Ioc.mpr ⟨product_gt s N k hk (fun n hn => (hs n hn).1) f hf, ?_⟩
  simpa only [mul_pow] using product_le s k (2 * N) (fun n hn => (hs n hn).2) f hf

theorem expansion (s : Finset ℕ) (N k : ℕ) (coeff : ℕ → ℂ) (t : ℝ)
    (hk : 1 ≤ k) (hs : ∀ n ∈ s, N < n ∧ n ≤ 2 * N) :
    exponentialSum151 s coeff (fun n => Real.log n) t ^ k =
      exponentialSum151 (Finset.Ioc (N ^ k) (2 ^ k * N ^ k))
        (coefficient s k coeff) (fun n => Real.log n) t :=
  DirichletPowerExpansion.exponential_power s _ k coeff t
    (fun n hn => Nat.zero_le N |>.trans_lt (hs n hn).1)
    (product_mem s N k hk hs)

theorem energy_bound (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (s : Finset ℕ) (N : ℕ) (coeff : ℕ → ℂ),
      (∀ n ∈ s, N < n ∧ n ≤ 2 * N) →
      (∑ n ∈ Finset.Ioc (N ^ k) (2 ^ k * N ^ k), ‖coefficient s k coeff n‖ ^ 2) ≤
        D * (2 * (N : ℝ)) ^ ε * (∑ n ∈ s, ‖coeff n‖ ^ 2) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨D, hD, he⟩ := DirichletPowerEnergy.energy_bound k hk (ε / k) (div_pos hε hkpos)
  refine ⟨D, hD, ?_⟩
  intro s N coeff hs
  have hsub : Finset.Ioc (N ^ k) (2 ^ k * N ^ k) ⊆ Finset.Icc 1 ((2 * N) ^ k) := by
    intro n hn
    have hh := Finset.mem_Ioc.mp hn
    refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
    simpa only [mul_pow] using hh.2
  have hh := (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => sq_nonneg ‖coefficient s k coeff n‖)).trans
      (he s (2 * N) coeff (fun n hn => ⟨by have := (hs n hn).1; omega, (hs n hn).2⟩))
  convert hh using 1
  congr 2
  rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by positivity)]
  congr 1
  field_simp

end DirichletPowerSupport

#print axioms DirichletPowerSupport.energy_bound
run_cmd do
  for decl in [``DirichletPowerSupport.expansion, ``DirichletPowerSupport.energy_bound] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "DIRICHLET POWER SUPPORT PASSED"
