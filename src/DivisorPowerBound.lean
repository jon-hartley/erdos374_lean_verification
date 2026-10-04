import PowerDifferenceParameters

/-!
The number of divisors is bounded by any fixed positive power, with a
constant depending only on that power. This supplies coefficient bounds
for finite Dirichlet convolutions without an analytic assumption.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter
open scoped BigOperators

namespace DivisorPowerBound

theorem linear_le_geometric (r : ℝ) (hr : 1 < r) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ, (k : ℝ) + 1 ≤ C * r ^ k := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨max ((K : ℝ) + 2) 2, by have := le_max_right ((K : ℝ) + 2) 2; linarith, ?_⟩
  intro k
  have hpow : 1 ≤ r ^ k := one_le_pow₀ hr.le
  by_cases hk : K ≤ k ∧ 1 ≤ k
  · have hh := hK k hk.1
    simp only [pow_one] at hh
    have hkr : (k : ℝ) ≤ r ^ k := ((div_lt_one (by positivity)).mp hh).le
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.2
    have hC : 2 ≤ max ((K : ℝ) + 2) 2 := le_max_right _ _
    nlinarith
  · have hsmall : (k : ℝ) + 1 ≤ (K : ℝ) + 2 := by
      exact_mod_cast (show k + 1 ≤ K + 2 by omega)
    have hC : (K : ℝ) + 2 ≤ max ((K : ℝ) + 2) 2 := le_max_left _ _
    have hCp : 0 ≤ max ((K : ℝ) + 2) 2 := by positivity
    nlinarith

theorem successor_le_two_pow (k : ℕ) : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    push_cast
    rw [pow_succ]
    have hh : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    nlinarith

theorem exists_prime_factor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ p k : ℕ, 2 ≤ p →
      (k : ℝ) + 1 ≤ (if p < P then C else 1) * ((p : ℝ) ^ k) ^ ε := by
  have hr : 1 < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  obtain ⟨C, hC, hgeom⟩ := linear_le_geometric ((2 : ℝ) ^ ε) hr
  have hlim : Tendsto (fun p : ℕ => (p : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨P, hP⟩ := eventually_atTop.mp (hlim.eventually (eventually_ge_atTop 2))
  refine ⟨P, C, hC, ?_⟩
  intro p k hp
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have heq : ((p : ℝ) ^ k) ^ ε = ((p : ℝ) ^ ε) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0, mul_comm,
      Real.rpow_mul hp0, Real.rpow_natCast]
  rw [heq]
  by_cases hsmall : p < P
  · rw [ite_eq_left hsmall]
    apply (hgeom k).trans
    gcongr
  · rw [ite_eq_right hsmall, one_mul]
    exact (successor_le_two_pow k).trans
      (pow_le_pow_left₀ (by norm_num) (hP p (by omega)) k)

theorem divisor_count_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      (n.divisors.card : ℝ) ≤ D * (n : ℝ) ^ ε := by
  classical
  obtain ⟨P, C, hC, hfactor⟩ := exists_prime_factor_bound ε hε
  have hCpos : 0 < C := by linarith
  refine ⟨C ^ P, by positivity, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow hε.ne']
  have hprod : (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = n := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  have hcount : (n.primeFactors.filter (fun p => p < P)).card ≤ P := by
    have hh : n.primeFactors.filter (fun p => p < P) ⊆ Finset.range P := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa only [Finset.card_range] using Finset.card_le_card hh
  have hconstants : (∏ p ∈ n.primeFactors, if p < P then C else 1) ≤ C ^ P := by
    rw [← Finset.prod_filter, Finset.prod_const]
    exact pow_le_pow_right₀ hC hcount
  calc
    _ = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn, Nat.cast_prod]
      simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < P then C else 1) * ((p : ℝ) ^ n.factorization p) ^ ε := by
      apply Finset.prod_le_prod₀
      · intro p _
        positivity
      · intro p hp
        exact hfactor p (n.factorization p) (Nat.prime_of_mem_primeFactors hp).two_le
    _ = (∏ p ∈ n.primeFactors, if p < P then C else 1) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ (by
        intro p _
        positivity) ε, hprod]
    _ ≤ _ := mul_le_mul_of_nonneg_right hconstants (Real.rpow_nonneg (Nat.cast_nonneg n) ε)

end DivisorPowerBound

#print axioms DivisorPowerBound.divisor_count_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``DivisorPowerBound.divisor_count_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "DIVISOR POWER BOUND PASSED"
