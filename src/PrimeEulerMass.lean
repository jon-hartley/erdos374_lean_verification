import PrimeEulerDimensionOne
import SieveStoppingRecurrence

/-! Exact cumulative masses of the prime measure appearing in the first-prime
Rosser recurrence, and its unconditional dimension-one comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
namespace PrimeEulerMass
open SieveStoppingExpansion SieveStoppingRecurrence PrimeEulerLogBounds

def weight (p : ℕ) : ℝ := (p:ℝ)⁻¹ * primeEuler (p:ℝ)

theorem weight_nonneg (p : ℕ) : 0 ≤ weight p :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) (SieveEulerRatio.euler_pos _).le

theorem firstSteps_euler_sum (ps : List ℕ) (b : ℕ → ℝ) (hnd : ps.Nodup) :
    ((firstSteps ps).map (fun v => b v.1 * SievePrefixLoss.euler v.2 b)).sum =
      1 - SievePrefixLoss.euler ps b := by
  induction ps with
  | nil => simp [firstSteps, SievePrefixLoss.euler]
  | cons p ps ih =>
    obtain ⟨hp, hn⟩ := List.nodup_cons.mp hnd
    simp only [firstSteps, List.map_cons, List.sum_cons, ih hn,
      SievePrefixLoss.euler_cons p ps b hp]
    ring

theorem prefix_mass (z : ℝ) :
    ∑ p ∈ SieveSmallWeights.pool z, weight p = 1-primeEuler z := by
  have hm : ((firstSteps (SieveSmallWeights.primes z)).map
      (fun v => (v.1:ℝ)⁻¹ * SievePrefixLoss.euler v.2 (fun p => (p:ℝ)⁻¹))) =
      ((firstSteps (SieveSmallWeights.primes z)).map (fun v => weight v.1)) := by
    apply List.map_congr_left
    intro v hv
    rw [(prime_firstSteps_tail z v hv).2]
    rfl
  have hh := congrArg (fun l : List ℕ => (l.map weight).sum)
    (firstSteps_heads (SieveSmallWeights.primes z))
  simp only [List.map_map, Function.comp_def] at hh
  have h := firstSteps_euler_sum (SieveSmallWeights.primes z)
    (fun p => (p:ℝ)⁻¹) (SieveSmallWeights.primes_nodup z)
  rw [hm, hh] at h
  rw [← List.sum_toFinset _ (SieveSmallWeights.primes_nodup z),
    SieveSmallWeights.primes_toFinset] at h
  exact h

theorem interval_mass (a b : ℝ) (hab : a ≤ b) :
    ∑ p ∈ intervalPrimes a b, weight p = primeEuler a-primeEuler b := by
  have hs : SieveSmallWeights.pool b =
      SieveSmallWeights.pool a ∪ intervalPrimes a b := by
    simpa only [one_pow, Real.rpow_one, intervalPrimes] using
      SieveEulerRatio.pool_split a 1 b (by simpa using hab)
  have hd : Disjoint (SieveSmallWeights.pool a) (intervalPrimes a b) := by
    simpa only [one_pow, Real.rpow_one, intervalPrimes] using SieveEulerRatio.pools_disjoint a 1 b
  have h := prefix_mass b
  rw [hs, Finset.sum_union hd, prefix_mass a] at h
  linarith

theorem normalized_interval_mass (a b : ℝ) (hab : a ≤ b) :
    (∑ p ∈ intervalPrimes a b, weight p / primeEuler b) =
      primeEuler a / primeEuler b - 1 := by
  rw [← Finset.sum_div, interval_mass a b hab, sub_div,
    div_self (SieveEulerRatio.euler_pos b).ne']

theorem normalized_interval_bound (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ intervalPrimes a b, weight p / primeEuler b) ≤
      Real.log b / Real.log a - 1 +
        PrimeEulerDimensionOne.errorConstant * Real.log b / (Real.log a)^2 := by
  rw [normalized_interval_mass a b hab]
  have h := PrimeEulerDimensionOne.ratio_bound a b ha hab
  have hid : (Real.log b / Real.log a) *
      (1 + PrimeEulerDimensionOne.errorConstant / Real.log a) - 1 =
      Real.log b / Real.log a - 1 +
        PrimeEulerDimensionOne.errorConstant * Real.log b / (Real.log a)^2 := by
    ring
  linarith

run_cmd do
  for decl in [``weight_nonneg, ``firstSteps_euler_sum, ``prefix_mass, ``interval_mass,
    ``normalized_interval_mass, ``normalized_interval_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end PrimeEulerMass
end
