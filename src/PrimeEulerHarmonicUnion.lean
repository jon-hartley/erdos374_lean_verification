import PrimeEulerHarmonicSmooth

/-! The excluded-prime union bound with exact inclusive integer endpoints.
No uniqueness of a large prime divisor is used. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace PrimeEulerHarmonicUnion
open PrimeEulerHarmonicSmooth SieveStoppingExpansion

theorem harmonic_eq_real_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ Finset.Icc 1 N, (n:ℝ)⁻¹ := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem multiples_sum (p N : ℕ) (hp : 0 < p) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n), (n:ℝ)⁻¹) =
      (p:ℝ)⁻¹*(harmonic (N/p):ℝ) := by
  have he : (∑ k ∈ Finset.Icc 1 (N/p), ((p*k:ℕ):ℝ)⁻¹) =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n), (n:ℝ)⁻¹ := by
    apply Finset.sum_bij (fun k _ => p*k)
    · intro k hk
      obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right p k⟩
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hkN
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hp hab
    · intro n hn
      obtain ⟨hn, hd⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
      refine ⟨n/p, Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnN⟩, Nat.mul_div_cancel' hd⟩
      exact Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp
    · intro k _
      rfl
  rw [← he, harmonic_eq_real_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Nat.cast_mul, mul_inv_rev]
  ring

theorem nonsmooth_prime (z : ℝ) (N n : ℕ) (hn : n ∈ Finset.Icc 1 N)
    (hns : n ∉ Nat.factoredNumbers (SieveSmallWeights.pool z)) :
    ∃ p ∈ excludedPrimes z N, p ∣ n := by
  have he : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p ∉ SieveSmallWeights.pool z := by
    by_contra! hh
    apply hns
    rw [Nat.mem_factoredNumbers']
    exact hh
  obtain ⟨p, hp, hd, hnp⟩ := he
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hpN : p ≤ N := (Nat.le_of_dvd (by omega : 0 < n) hd).trans (Finset.mem_Icc.mp hn).2
  have hzp : z ≤ (p:ℝ) := by
    by_contra hz
    exact hnp ((SieveSmallWeights.mem_pool z p).mpr ⟨hp, lt_of_not_ge hz⟩)
  exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.pos, hpN⟩, hp, hzp⟩, hd⟩

theorem harmonic_union_bound (z : ℝ) (N : ℕ) :
    (harmonic N:ℝ) ≤
      (∑ n ∈ smoothBelow z N, (n:ℝ)⁻¹) +
      ∑ p ∈ excludedPrimes z N, (p:ℝ)⁻¹*(harmonic (N/p):ℝ) := by
  have hn : ∀ n ∈ Finset.Icc 1 N,
      (n:ℝ)⁻¹ ≤ (if n ∈ Nat.factoredNumbers (SieveSmallWeights.pool z) then (n:ℝ)⁻¹ else 0)+
        ∑ p ∈ excludedPrimes z N, if p ∣ n then (n:ℝ)⁻¹ else 0 := by
    intro n hn
    by_cases hs : n ∈ Nat.factoredNumbers (SieveSmallWeights.pool z)
    · simp only [hs, ite_true]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun p _ => by split_ifs <;> positivity))
    · obtain ⟨p, hp, hd⟩ := nonsmooth_prime z N n hn hs
      have hh := Finset.single_le_sum
        (f := fun p : ℕ => if p ∣ n then (n:ℝ)⁻¹ else 0)
        (fun p _ => by split_ifs <;> positivity) hp
      simpa only [hs, hd, ite_false, ite_true, zero_add] using hh
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        ((if n ∈ Nat.factoredNumbers (SieveSmallWeights.pool z) then (n:ℝ)⁻¹ else 0)+
        ∑ p ∈ excludedPrimes z N, if p ∣ n then (n:ℝ)⁻¹ else 0) := by
      rw [harmonic_eq_real_sum]
      exact Finset.sum_le_sum hn
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      · exact (Finset.sum_filter _ _).symm
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p hp
        rw [← Finset.sum_filter]
        exact multiples_sum p N (Finset.mem_filter.mp hp).2.1.pos

theorem inverse_lower_finite (z : ℝ) (N : ℕ) :
    (harmonic N:ℝ) -
      (∑ p ∈ excludedPrimes z N, (p:ℝ)⁻¹*(harmonic (N/p):ℝ)) ≤
      (primeEuler z)⁻¹ := by
  have hu := harmonic_union_bound z N
  have hs := smooth_sum_le_inverse z N
  linarith

theorem inverse_lower_real (z x : ℝ) :
    (harmonic ⌊x⌋₊:ℝ) -
      (∑ p ∈ excludedPrimes z ⌊x⌋₊, (p:ℝ)⁻¹*(harmonic ⌊x/(p:ℝ)⌋₊:ℝ)) ≤
      (primeEuler z)⁻¹ := by
  simpa only [Nat.floor_div_natCast] using inverse_lower_finite z ⌊x⌋₊

run_cmd do
  for decl in [``harmonic_eq_real_sum, ``multiples_sum, ``nonsmooth_prime,
      ``harmonic_union_bound, ``inverse_lower_finite, ``inverse_lower_real] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT EXCLUDED-PRIME HARMONIC UNION BOUND; CLOSED DIVISOR ENDPOINTS"

end PrimeEulerHarmonicUnion
end
