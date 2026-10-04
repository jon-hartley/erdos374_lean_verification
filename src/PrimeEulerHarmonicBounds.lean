import PrimeEulerHarmonicUnion

/-! Harmonic floor bounds reduce the actual Euler inverse to a weighted
sum over excluded primes. All endpoints remain those of the finite union bound. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real
open scoped BigOperators
namespace PrimeEulerHarmonicBounds
open PrimeEulerHarmonicSmooth PrimeEulerHarmonicUnion SieveStoppingExpansion

theorem excluded_properties (z x : ℝ) (hx : 0 ≤ x) (p : ℕ)
    (hp : p ∈ excludedPrimes z ⌊x⌋₊) :
    p.Prime ∧ z ≤ (p:ℝ) ∧ (p:ℝ) ≤ x := by
  obtain ⟨hm, hpp, hzp⟩ := Finset.mem_filter.mp hp
  refine ⟨hpp, hzp, ?_⟩
  have hpn : (p:ℝ) ≤ (⌊x⌋₊:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).2
  exact hpn.trans (Nat.floor_le hx)

theorem excluded_harmonic_le (z x : ℝ) (hx : 0 ≤ x) :
    (∑ p ∈ excludedPrimes z ⌊x⌋₊, (p:ℝ)⁻¹*(harmonic ⌊x/(p:ℝ)⌋₊:ℝ)) ≤
      ∑ p ∈ excludedPrimes z ⌊x⌋₊, (p:ℝ)⁻¹*(1+log x-log (p:ℝ)) := by
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpp, _hzp, hpx⟩ := excluded_properties z x hx p hp
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
  have hx0 : 0 < x := hp0.trans_le hpx
  have hdiv : (1:ℝ) ≤ x/(p:ℝ) := (le_div_iff₀ hp0).mpr (by simpa using hpx)
  have hh := harmonic_floor_le_one_add_log (x/(p:ℝ)) hdiv
  rw [log_div hx0.ne' hp0.ne'] at hh
  convert mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hp0.le) using 1
  ring

theorem inverse_lower_log (z x : ℝ) (hx : 0 ≤ x) :
    log x-(∑ p ∈ excludedPrimes z ⌊x⌋₊,
      (p:ℝ)⁻¹*(1+log x-log (p:ℝ))) ≤ (primeEuler z)⁻¹ := by
  have h0 := log_le_harmonic_floor x hx
  have h1 := inverse_lower_real z x
  have h2 := excluded_harmonic_le z x hx
  linarith

theorem inverse_lower_log_square (z : ℝ) :
    2*log z-(∑ p ∈ excludedPrimes z ⌊z^2⌋₊,
      (p:ℝ)⁻¹*(1+2*log z-log (p:ℝ))) ≤ (primeEuler z)⁻¹ := by
  simpa only [log_pow, Nat.cast_ofNat] using inverse_lower_log z (z^2) (sq_nonneg z)

run_cmd do
  for decl in [``excluded_properties, ``excluded_harmonic_le,
      ``inverse_lower_log, ``inverse_lower_log_square] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL EULER INVERSE REDUCED TO A CLOSED-ENDPOINT WEIGHTED PRIME SUM"

end PrimeEulerHarmonicBounds
end
