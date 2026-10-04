import PrimeEulerExponentialBound

/-! The actual accepted first-prime exponential sum, with its cubic cutoff
and Euler normalization retained. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open Real Set

namespace PrimeEulerAcceptedInner
open SieveStoppingExpansion PrimeEulerExponentialCalculus

def acceptedPrimes (T z : ℝ) : Finset ℕ :=
  (SieveSmallWeights.pool z).filter (fun q => (q : ℝ)^3 < T)

def cutoff (T z : ℝ) : ℝ := min z (exp (log T / 3))

def acceptedExponentialMass (T z : ℝ) : ℝ :=
  ∑ q ∈ acceptedPrimes T z,
    exp (-(log (T/(q : ℝ)) / log (q : ℝ))) *
      (PrimeEulerMass.weight q / primeEuler z)

theorem cube_lt_iff_lt_exp (T q : ℝ) (hT : 0 < T) (hq : 0 < q) :
    q^3 < T ↔ q < exp (log T / 3) := by
  rw [← log_lt_log_iff (pow_pos hq 3) hT, log_pow,
    ← log_lt_iff_lt_exp hq]
  norm_num
  constructor <;> intro h <;> linarith

theorem cutoff_eq_rpow (T z : ℝ) (hT : 0 < T) :
    cutoff T z = min z (T ^ (1/3 : ℝ)) := by
  rw [cutoff, rpow_def_of_pos hT]
  congr 2
  ring

theorem cutoff_pos (T z : ℝ) (hz : 0 < z) : 0 < cutoff T z :=
  lt_min hz (exp_pos _)

theorem cutoff_le (T z : ℝ) : cutoff T z ≤ z := min_le_left _ _

theorem acceptedPrimes_eq_pool (T z : ℝ) (hT : 0 < T) :
    acceptedPrimes T z = SieveSmallWeights.pool (cutoff T z) := by
  classical
  ext q
  rw [acceptedPrimes, Finset.mem_filter, SieveSmallWeights.mem_pool,
    SieveSmallWeights.mem_pool]
  constructor
  · rintro ⟨⟨hq, hqz⟩, hqT⟩
    exact ⟨hq, lt_min hqz ((cube_lt_iff_lt_exp T q hT
      (by exact_mod_cast hq.pos)).mp hqT)⟩
  · rintro ⟨hq, hqc⟩
    have hh := lt_min_iff.mp hqc
    exact ⟨⟨hq, hh.1⟩, (cube_lt_iff_lt_exp T q hT
      (by exact_mod_cast hq.pos)).mpr hh.2⟩

theorem child_exponential_eq_test (T q : ℝ) (hT : 0 < T) (hq : 1 < q) :
    exp (-(log (T/q)/log q)) = test (log T) q := by
  have hq0 : q ≠ 0 := by linarith
  have hl : log q ≠ 0 := (log_pos hq).ne'
  unfold test
  rw [log_div hT.ne' hq0]
  congr 1
  field_simp
  ring

/-- Exact renormalization at the complete accepted-prime cutoff. -/
theorem acceptedExponentialMass_eq (T z : ℝ) (hT : 0 < T) :
    acceptedExponentialMass T z =
      (primeEuler (cutoff T z) / primeEuler z) *
        ∑ q ∈ SieveSmallWeights.pool (cutoff T z),
          test (log T) q * (PrimeEulerMass.weight q / primeEuler (cutoff T z)) := by
  unfold acceptedExponentialMass
  rw [acceptedPrimes_eq_pool T z hT, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hp := ((SieveSmallWeights.mem_pool (cutoff T z) q).mp hq).1
  rw [child_exponential_eq_test T q hT (by exact_mod_cast hp.one_lt)]
  have hc := (SieveEulerRatio.euler_pos (cutoff T z)).ne'
  have hz := (SieveEulerRatio.euler_pos z).ne'
  field_simp

theorem prime_exponential_sum_nonneg (A z : ℝ) :
    0 ≤ ∑ q ∈ SieveSmallWeights.pool z,
      test A q * (PrimeEulerMass.weight q / primeEuler z) := by
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (test_pos A q).le
    (div_nonneg (PrimeEulerMass.weight_nonneg q) (SieveEulerRatio.euler_pos z).le)

theorem pool_empty_of_le_two (z : ℝ) (hz : z ≤ 2) :
    SieveSmallWeights.pool z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨hp, hlt⟩ := (SieveSmallWeights.mem_pool z q).mp hq
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hp.two_le
  linarith

theorem acceptedExponentialMass_eq_zero (T z : ℝ) (hT : 0 < T)
    (hc : cutoff T z ≤ 2) : acceptedExponentialMass T z = 0 := by
  rw [acceptedExponentialMass_eq T z hT, pool_empty_of_le_two _ hc]
  simp

/-- The inner bound before parameter simplification. The only arithmetic
inputs are the proved dimension-one ratio and actual exponential prime sum. -/
theorem accepted_exponential_bound_cutoff (T z : ℝ) (hT : 1 < T)
    (hc : 2 ≤ cutoff T z) :
    acceptedExponentialMass T z ≤
      ((log z / log (cutoff T z)) *
        (1 + PrimeEulerDimensionOne.errorConstant / log (cutoff T z))) *
      (exp (1-log T/log (cutoff T z)) *
        (1/(log T/log (cutoff T z)) +
          (PrimeEulerDimensionOne.errorConstant/log (cutoff T z)) *
            (1+2*(log T/log (cutoff T z)+1)/(log T/log (cutoff T z))^2))) := by
  rw [acceptedExponentialMass_eq T z (by linarith)]
  have hr := PrimeEulerDimensionOne.ratio_bound (cutoff T z) z hc (cutoff_le T z)
  have hs := PrimeEulerExponentialBound.prime_exponential_sum_le
    (log T) (cutoff T z) (log_pos hT) hc
  apply mul_le_mul hr hs (prime_exponential_sum_nonneg _ _)
  exact (div_pos (SieveEulerRatio.euler_pos _) (SieveEulerRatio.euler_pos _)).le.trans hr

theorem log_cutoff (T z : ℝ) (hz : 0 < z) :
    log (cutoff T z) = min (log z) (log T / 3) := by
  rcases le_total z (exp (log T / 3)) with h | h
  · have hh := log_le_log hz h
    rw [log_exp] at hh
    rw [cutoff, min_eq_left h, min_eq_left hh]
  · have hh := log_le_log (exp_pos (log T / 3)) h
    rw [log_exp] at hh
    rw [cutoff, min_eq_right h, log_exp, min_eq_right hh]

run_cmd do
  for decl in [``cube_lt_iff_lt_exp, ``cutoff_eq_rpow, ``cutoff_pos, ``cutoff_le,
    ``acceptedPrimes_eq_pool, ``child_exponential_eq_test, ``acceptedExponentialMass_eq,
    ``prime_exponential_sum_nonneg, ``pool_empty_of_le_two,
    ``acceptedExponentialMass_eq_zero, ``accepted_exponential_bound_cutoff, ``log_cutoff] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ACCEPTED-PRIME CUTOFF AND EXPONENTIAL BOUND PASSED"

end PrimeEulerAcceptedInner
end
