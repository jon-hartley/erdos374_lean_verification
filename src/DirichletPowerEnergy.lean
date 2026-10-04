import DirichletPowerCoefficients

/-!
Uniform energy control for a fixed positive power of a Dirichlet
polynomial. The arbitrary positive loss is in the product length.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace DirichletPowerEnergy
open DirichletPowerCoefficients

theorem divisor_power_bound (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      (n.divisors.card : ℝ) ^ k ≤ D * (n : ℝ) ^ ε := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨C, hC, hcount⟩ := DivisorPowerBound.divisor_count_bound
    (ε / k) (div_pos hε hkpos)
  refine ⟨C ^ k, by positivity, ?_⟩
  intro n
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg n.divisors.card) (hcount n) k
  rw [mul_pow] at hh
  convert hh using 1
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  rw [div_mul_cancel₀ ε hkpos.ne']

theorem energy_bound (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (s : Finset ℕ) (L : ℕ) (coeff : ℕ → ℂ),
      (∀ n ∈ s, 0 < n ∧ n ≤ L) →
      (∑ n ∈ Finset.Icc 1 (L ^ k), ‖coefficient s k coeff n‖ ^ 2) ≤
        D * ((L ^ k : ℕ) : ℝ) ^ ε * (∑ n ∈ s, ‖coeff n‖ ^ 2) ^ k := by
  obtain ⟨D, hD, hdiv⟩ := divisor_power_bound k hk ε hε
  refine ⟨D, hD, ?_⟩
  intro s L coeff hs
  have hmap : ∀ f ∈ tuples s k, productIndex f ∈ Finset.Icc 1 (L ^ k) := by
    intro f hf
    exact Finset.mem_Icc.mpr ⟨product_positive s k (fun n hn => (hs n hn).1) f hf,
      product_le s k L (fun n hn => (hs n hn).2) f hf⟩
  apply DirichletPowerCoefficients.energy_bound s (Finset.Icc 1 (L ^ k)) k coeff
    (D * ((L ^ k : ℕ) : ℝ) ^ ε) hmap
  intro n hn
  have hnb := Finset.mem_Icc.mp hn
  have hcast : (n : ℝ) ≤ (L ^ k : ℕ) := by exact_mod_cast hnb.2
  calc
    _ ≤ (n.divisors.card : ℝ) ^ k := by
      exact_mod_cast fiber_card_bound s k n (by omega)
    _ ≤ D * (n : ℝ) ^ ε := hdiv n
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) hcast hε.le) hD.le

end DirichletPowerEnergy

#print axioms DirichletPowerEnergy.energy_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``DirichletPowerEnergy.energy_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "DIRICHLET POWER ENERGY PASSED"
