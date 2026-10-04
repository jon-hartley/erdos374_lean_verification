import SieveEulerRatio

/-! The actual decreasing prime list splits at the small-prime cutoff, with
the large-prime list first. The threshold belongs to the large list; both
lists exclude the final upper endpoint. Only the cutoff ordering is required. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace SievePrimeListSplit

theorem large_primes_toFinset (D s z : ℝ) :
    (SieveBoxedFamily.primes D s z).toFinset = SieveBoxedFamily.pool D s z :=
  SieveBoxTuples.descending_toFinset _

theorem large_mem_primes (D s z : ℝ) (p : ℕ) :
    p ∈ SieveBoxedFamily.primes D s z ↔
      p.Prime ∧ (p : ℝ) < z ∧ D^(s^2) ≤ (p : ℝ) := by
  rw [← List.mem_toFinset, large_primes_toFinset, SieveBoxedFamily.mem_pool]

theorem large_primes_nodup (D s z : ℝ) :
    (SieveBoxedFamily.primes D s z).Nodup :=
  SieveBoxTuples.descending_nodup _

theorem large_primes_descending (D s z : ℝ) :
    (SieveBoxedFamily.primes D s z).Pairwise (· ≥ ·) :=
  SieveBoxTuples.descending_pairwise _

theorem large_gt_small (D s z : ℝ) (p q : ℕ)
    (hp : p ∈ SieveBoxedFamily.primes D s z)
    (hq : q ∈ SieveSmallWeights.primes (D^(s^2))) : q < p := by
  have hpu := ((large_mem_primes D s z p).mp hp).2.2
  have hqu := ((SieveSmallWeights.mem_primes (D^(s^2)) q).mp hq).2
  exact_mod_cast hqu.trans_le hpu

theorem append_nodup (D s z : ℝ) :
    (SieveBoxedFamily.primes D s z ++
      SieveSmallWeights.primes (D^(s^2))).Nodup := by
  apply List.nodup_append.mpr
  exact ⟨large_primes_nodup D s z, SieveSmallWeights.primes_nodup _,
    fun p hp q hq => ne_of_gt (large_gt_small D s z p q hp hq)⟩

theorem append_descending (D s z : ℝ) :
    (SieveBoxedFamily.primes D s z ++
      SieveSmallWeights.primes (D^(s^2))).Pairwise (· ≥ ·) := by
  apply List.pairwise_append.mpr
  exact ⟨large_primes_descending D s z, SieveSmallWeights.primes_descending _,
    fun p hp q hq => (large_gt_small D s z p q hp hq).le⟩

/-- Exact ordered concatenation, including all endpoint and empty-list cases. -/
theorem primes_split (D s z : ℝ) (hu : D^(s^2) ≤ z) :
    SieveSmallWeights.primes z = SieveBoxedFamily.primes D s z ++
      SieveSmallWeights.primes (D^(s^2)) := by
  have hset : (SieveSmallWeights.primes z).toFinset =
      (SieveBoxedFamily.primes D s z ++
        SieveSmallWeights.primes (D^(s^2))).toFinset := by
    rw [List.toFinset_append, large_primes_toFinset,
      SieveSmallWeights.primes_toFinset, SieveSmallWeights.primes_toFinset,
      SieveEulerRatio.pool_split D s z hu, Finset.union_comm]
  exact (List.perm_of_nodup_nodup_toFinset_eq
    (SieveSmallWeights.primes_nodup z) (append_nodup D s z) hset).eq_of_pairwise'
      (SieveSmallWeights.primes_descending z) (append_descending D s z)

theorem reciprocal_prime_bounds (p : ℕ) (hp : p.Prime) :
    0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  refine ⟨inv_nonneg.mpr (Nat.cast_nonneg p), ?_⟩
  simpa only [inv_one] using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hp1

theorem reciprocal_bounds (z : ℝ) (p : ℕ)
    (hp : p ∈ SieveSmallWeights.primes z) :
    0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 :=
  reciprocal_prime_bounds p (SieveSmallWeights.primes_prime z p hp)

theorem large_reciprocal_bounds (D s z : ℝ) (p : ℕ)
    (hp : p ∈ SieveBoxedFamily.primes D s z) :
    0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 :=
  reciprocal_prime_bounds p ((large_mem_primes D s z p).mp hp).1

run_cmd do
  for decl in [``large_primes_toFinset, ``large_mem_primes, ``large_primes_nodup,
    ``large_primes_descending, ``large_gt_small, ``append_nodup, ``append_descending,
    ``primes_split, ``reciprocal_prime_bounds, ``reciprocal_bounds,
    ``large_reciprocal_bounds] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT ORDERED PRIME LIST SPLIT: STANDARD AXIOMS ONLY"

end SievePrimeListSplit
end
