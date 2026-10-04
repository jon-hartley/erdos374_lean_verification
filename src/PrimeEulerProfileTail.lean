import SieveProfileTailScalar
import PrimeEulerExponentialBound

/-! Actual finite prime sums used to bound the large child-ratio tail.
No continuum density equality or weighted moment at an invalid parameter
range is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real
open scoped BigOperators
namespace PrimeEulerProfileTail
open SieveStoppingExpansion PrimeEulerExponentialCalculus

def outerReciprocal (z : ℝ) (q : ℕ) : ℝ :=
  ∑ p ∈ (SieveSmallWeights.pool z).filter (fun p => q < p), (p:ℝ)⁻¹

theorem outerReciprocal_bound (z : ℝ) (q : ℕ)
    (hq : q ∈ SieveSmallWeights.pool z) (hlog : 400 ≤ log z) :
    outerReciprocal z q ≤ (2/5:ℝ)*(log z/log (q:ℝ)) := by
  obtain ⟨hqp, hqz⟩ := (SieveSmallWeights.mem_pool z q).mp hq
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hqp.two_le
  have hq0 : (0:ℝ) < q := by linarith
  have hlq : 0 < log (q:ℝ) := log_pos (by linarith)
  have hlz : 0 < log z := by linarith
  have hh := MertensPrimeInterval.prime_reciprocal_interval (q:ℝ) z
    ((SieveSmallWeights.pool z).filter (fun p => q < p)) (by linarith) hqz.le (by
      intro p hp
      obtain ⟨hpz, hqp⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpp, hpz⟩ := (SieveSmallWeights.mem_pool z p).mp hpz
      exact ⟨hpp, by exact_mod_cast hqp.le, hpz.le⟩)
  have hlogbound := SieveProfileTailScalar.log_le_three_eighths
    (log z/log (q:ℝ)) (div_pos hlz hlq)
  have he : 10/log (q:ℝ) ≤ (1/40:ℝ)*(log z/log (q:ℝ)) := by
    apply (div_le_iff₀ hlq).mpr
    have hid : ((1/40:ℝ)*(log z/log (q:ℝ)))*log (q:ℝ) = log z/40 := by field_simp
    rw [hid]
    linarith
  unfold outerReciprocal
  linarith

theorem weighted_test_bound (A z q : ℝ) (hz : 1 < z) (hq : 1 < q)
    (hA : (1/10:ℝ) ≤ A/log z) :
    (log z/log q)*test A q ≤ 20*exp (-1)*test (A/2) q := by
  have hlz : 0 < log z := log_pos hz
  have hlq : 0 < log q := log_pos hq
  have hAm := (le_div_iff₀ hlz).mp hA
  have hx : log z/log q ≤ 10*(A/log q) := by
    apply (div_le_iff₀ hlq).mpr
    have heq : (10*(A/log q))*log q = 10*A := by field_simp
    rw [heq]
    linarith
  have hh := SieveProfileTailScalar.weighted_exp_bound (log z/log q) (A/log q) hx
  apply hh.trans_eq
  unfold test
  rw [mul_assoc, ← exp_add]
  congr 1
  congr 1
  ring

theorem small_parameter_sum_bound (A z : ℝ) (hz : 2 ≤ z)
    (hA : (1/10:ℝ) ≤ A/log z) :
    (∑ q ∈ SieveSmallWeights.pool z, test (A/2) q*
      (PrimeEulerMass.weight q/primeEuler z)) ≤
      exp 1*(20+841*(PrimeEulerDimensionOne.errorConstant/log z)) := by
  have hlz : 0 < log z := log_pos (by linarith)
  have hAm := (le_div_iff₀ hlz).mp hA
  have hA0 : 0 < A := by nlinarith
  have hx : (1/20:ℝ) ≤ (A/2)/log z := by
    rw [show (A/2)/log z = (A/log z)/2 by ring]
    linarith
  obtain ⟨h1, h2⟩ := SieveProfileTailScalar.reciprocal_parameter_bounds ((A/2)/log z) hx
  have he0 : 0 ≤ PrimeEulerDimensionOne.errorConstant/log z :=
    div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le hlz.le
  have hc : 1/((A/2)/log z)+(PrimeEulerDimensionOne.errorConstant/log z)*
      (1+2*((A/2)/log z+1)/((A/2)/log z)^2) ≤
        20+841*(PrimeEulerDimensionOne.errorConstant/log z) := by
    have hh := mul_le_mul_of_nonneg_left h2 he0
    nlinarith
  have hc0 : 0 ≤ 1/((A/2)/log z)+(PrimeEulerDimensionOne.errorConstant/log z)*
      (1+2*((A/2)/log z+1)/((A/2)/log z)^2) := by positivity
  apply (PrimeEulerExponentialBound.prime_exponential_sum_le (A/2) z (by linarith) hz).trans
  exact mul_le_mul (exp_le_exp.mpr (by linarith)) hc hc0 (exp_pos 1).le

theorem weighted_prime_sum_bound (A z : ℝ) (hz : 2 ≤ z)
    (hA : (1/10:ℝ) ≤ A/log z) :
    (∑ q ∈ SieveSmallWeights.pool z, (log z/log q)*test A q*
      (PrimeEulerMass.weight q/primeEuler z)) ≤
      20*(20+841*(PrimeEulerDimensionOne.errorConstant/log z)) := by
  have hs : (∑ q ∈ SieveSmallWeights.pool z, (log z/log q)*test A q*
      (PrimeEulerMass.weight q/primeEuler z)) ≤
      (20*exp (-1))*(∑ q ∈ SieveSmallWeights.pool z, test (A/2) q*
        (PrimeEulerMass.weight q/primeEuler z)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hq1 : (1:ℝ) < q := by exact_mod_cast ((SieveSmallWeights.mem_pool z q).mp hq).1.one_lt
    have hh := mul_le_mul_of_nonneg_right (weighted_test_bound A z q (by linarith) hq1 hA)
      (div_nonneg (PrimeEulerMass.weight_nonneg q) (SieveEulerRatio.euler_pos z).le)
    convert hh using 1; ring
  apply hs.trans
  apply (mul_le_mul_of_nonneg_left (small_parameter_sum_bound A z hz hA)
    (by positivity : 0 ≤ 20*exp (-1))).trans_eq
  have hid : exp (-1)*exp 1 = 1 := by rw [← exp_add]; norm_num
  calc
    _ = 20*(exp (-1)*exp 1)*(20+841*(PrimeEulerDimensionOne.errorConstant/log z)) := by ring
    _ = _ := by rw [hid]; ring

run_cmd do
  for decl in [``outerReciprocal_bound, ``weighted_test_bound,
    ``small_parameter_sum_bound, ``weighted_prime_sum_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL OUTER RECIPROCAL AND SMALL-PARAMETER EXPONENTIAL SUM BOUNDS"
end PrimeEulerProfileTail
end
