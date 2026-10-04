import SieveStoppingTwoStep
import PrimeEulerAcceptedMajorant
import PrimeEulerExponentialMoments
import RosserExponentialMoments
import PrimeEulerRosserInnerBound

/-! Assembly of the actual finite two-step stopping operator. The accepted
inner primes retain their cubic guard and exact Euler normalization. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Set
open scoped BigOperators

namespace SieveStoppingArithmeticContraction
open SieveStoppingExpansion PrimeEulerAcceptedInner PrimeEulerAcceptedParameters
open PrimeEulerExponentialCalculus

def exponential (T z : ℝ) : ℝ := exp (-(log T/log z))
def epsilon (z : ℝ) : ℝ := PrimeEulerDimensionOne.errorConstant/log z
def innerSum (A z : ℝ) : ℝ :=
  ∑ p ∈ SieveSmallWeights.pool z, RosserInnerIntegral.inner (A/log p-1)*
    (PrimeEulerMass.weight p/primeEuler z)
def weightedMoment (A z : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ SieveSmallWeights.pool z, (log z/log p)^n*test A p*
    (PrimeEulerMass.weight p/primeEuler z)

theorem epsilon_nonneg (z : ℝ) (hz : 2 ≤ z) : 0 ≤ epsilon z :=
  div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le (log_pos (by linarith)).le

theorem operator_factorization (T z : ℝ) :
    SieveStoppingTwoStep.operator exponential T z =
      ∑ p ∈ SieveSmallWeights.pool z,
        (PrimeEulerMass.weight p/primeEuler z)*acceptedExponentialMass (T/p) p := by
  classical
  unfold SieveStoppingTwoStep.operator
  apply Finset.sum_congr rfl
  intro p hp
  unfold acceptedExponentialMass acceptedPrimes
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with hg
  · have hpv : primeEuler (p:ℝ) ≠ 0 := (SieveEulerRatio.euler_pos _).ne'
    unfold PrimeEulerMass.weight exponential
    field_simp
  · simp

theorem child_parameter (T p : ℝ) (hT : 0 < T) (hp : 1 < p) :
    parameter (T/p) p = log T/log p-1 := by
  have hp0 : p ≠ 0 := by linarith
  have hlp : log p ≠ 0 := (log_pos hp).ne'
  unfold parameter
  rw [log_div hT.ne' hp0]
  field_simp

theorem epsilon_rescale (z p : ℝ) (hz : 1 < z) :
    PrimeEulerDimensionOne.errorConstant/log p = epsilon z*(log z/log p) := by
  have hlz : log z ≠ 0 := (log_pos hz).ne'
  unfold epsilon
  field_simp

theorem parameter_ge_two (T z : ℝ) (hz : 2 ≤ z) (hT : z^2 ≤ T) :
    2 ≤ log T/log z := by
  have hz0 : 0 < z := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  apply (le_div_iff₀ hlz).mpr
  have hh := log_le_log (pow_pos hz0 2) hT
  simpa only [log_pow, Nat.cast_ofNat] using hh

theorem operator_le_prime_sums (T z : ℝ) (hz : 2 ≤ z) (hT : z^2 ≤ T) :
    SieveStoppingTwoStep.operator exponential T z ≤ innerSum (log T) z +
      (20*exp 1*epsilon z)*weightedMoment (log T) z 1 +
      (51*exp 1*(epsilon z)^2)*weightedMoment (log T) z 2 := by
  have hz0 : 0 < z := by linarith
  have hT0 : 0 < T := (pow_pos hz0 2).trans_le hT
  rw [operator_factorization]
  calc
    _ ≤ ∑ p ∈ SieveSmallWeights.pool z, (PrimeEulerMass.weight p/primeEuler z)*
        (RosserInnerIntegral.inner (parameter (T/p) p) +
          20*exp 1*(PrimeEulerDimensionOne.errorConstant/log p)*exp (-parameter (T/p) p) +
          51*exp 1*(PrimeEulerDimensionOne.errorConstant/log p)^2*exp (-parameter (T/p) p)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpprime, hpz⟩ := (SieveSmallWeights.mem_pool z p).mp hp
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hpprime.two_le
      have hp0 : (0:ℝ) < p := by linarith
      have hpT : (p:ℝ) ≤ T/p := (le_div_iff₀ hp0).mpr (by nlinarith)
      exact mul_le_mul_of_nonneg_left
        (PrimeEulerAcceptedMajorant.accepted_exponential_majorant (T/p) p hp2 hpT)
        (div_nonneg (PrimeEulerMass.weight_nonneg p) (SieveEulerRatio.euler_pos z).le)
    _ = _ := by
      unfold innerSum weightedMoment
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      have hp1 : (1:ℝ) < p := by
        exact_mod_cast ((SieveSmallWeights.mem_pool z p).mp hp).1.one_lt
      have hc := child_parameter T p hT0 hp1
      have he : exp (-parameter (T/p) p) = test (log T) p :=
        child_exponential_eq_test T p hT0 hp1
      rw [he, hc, epsilon_rescale z p (by linarith)]
      ring

theorem weightedMoment_one_le (A z : ℝ) (hA : 0 < A) (hz : 2 ≤ z)
    (hr : 2 ≤ A/log z) :
    weightedMoment A z 1 ≤ exp (1-A/log z)*(3/4+(7/2)*epsilon z) := by
  have hh := PrimeEulerExponentialMoments.prime_moment_one_le A z hA hz hr
  have h1 := RosserExponentialMoments.normalized_poly1 (A/log z) hr
  have h2 := RosserExponentialMoments.normalized_poly2 (A/log z) hr
  have hε := epsilon_nonneg z hz
  have hb : (A/log z+1)/(A/log z)^2 + epsilon z*
      (1+2*((A/log z)^2+2*(A/log z)+2)/(A/log z)^3) ≤ 3/4+(7/2)*epsilon z := by
    have hm := mul_le_mul_of_nonneg_left h2 hε
    simp only [mul_div_assoc] at *
    nlinarith
  change weightedMoment A z 1 ≤ _
  have hraw : weightedMoment A z 1 ≤ exp (1-A/log z)*
      ((A/log z+1)/(A/log z)^2 + epsilon z*
        (1+2*((A/log z)^2+2*(A/log z)+2)/(A/log z)^3)) := by
    simpa only [weightedMoment, epsilon, pow_one] using hh
  exact hraw.trans (mul_le_mul_of_nonneg_left hb (exp_pos _).le)

theorem weightedMoment_two_le (A z : ℝ) (hA : 0 < A) (hz : 2 ≤ z)
    (hr : 2 ≤ A/log z) :
    weightedMoment A z 2 ≤ exp (1-A/log z)*(5/4+(23/4)*epsilon z) := by
  have hh := PrimeEulerExponentialMoments.prime_moment_two_le A z hA hz hr
  have h2 := RosserExponentialMoments.normalized_poly2 (A/log z) hr
  have h3 := RosserExponentialMoments.normalized_poly3 (A/log z) hr
  have hε := epsilon_nonneg z hz
  have hb : ((A/log z)^2+2*(A/log z)+2)/(A/log z)^3 + epsilon z*
      (1+2*((A/log z)^3+3*(A/log z)^2+6*(A/log z)+6)/(A/log z)^4) ≤
        5/4+(23/4)*epsilon z := by
    have hm := mul_le_mul_of_nonneg_left h3 hε
    simp only [mul_div_assoc] at *
    nlinarith
  have hraw : weightedMoment A z 2 ≤ exp (1-A/log z)*
      (((A/log z)^2+2*(A/log z)+2)/(A/log z)^3 + epsilon z*
        (1+2*((A/log z)^3+3*(A/log z)^2+6*(A/log z)+6)/(A/log z)^4)) := by
    simpa only [weightedMoment, epsilon] using hh
  exact hraw.trans (mul_le_mul_of_nonneg_left hb (exp_pos _).le)

theorem scalar_budget (e : ℝ) (he : 0 ≤ e) (hemax : e ≤ 1/100000) :
    (99/100:ℝ) + exp 2*((35/2)*e+(535/4)*e^2+(1173/4)*e^3) ≤ 199/200 := by
  have h2 : e^2 ≤ (1/100000:ℝ)^2 := pow_le_pow_left₀ he hemax 2
  have h3 : e^3 ≤ (1/100000:ℝ)^3 := pow_le_pow_left₀ he hemax 3
  have hp : (35/2)*e+(535/4)*e^2+(1173/4)*e^3 ≤
      (35/2)*(1/100000:ℝ)+(535/4)*(1/100000:ℝ)^2+(1173/4)*(1/100000:ℝ)^3 := by
    nlinarith
  have hp0 : 0 ≤ (35/2)*e+(535/4)*e^2+(1173/4)*e^3 := by positivity
  calc
    _ ≤ 99/100+(15/2)*((35/2)*(1/100000:ℝ)+(535/4)*(1/100000:ℝ)^2+
        (1173/4)*(1/100000:ℝ)^3) :=
      add_le_add le_rfl (mul_le_mul RosserKernelContraction.exp_two_le hp hp0 (by norm_num))
    _ ≤ _ := by norm_num

theorem epsilon_small (z : ℝ) (hz : 2 ≤ z)
    (hlog : 100000*PrimeEulerDimensionOne.errorConstant ≤ log z) :
    epsilon z ≤ 1/100000 := by
  unfold epsilon
  apply (div_le_iff₀ (log_pos (by linarith : 1 < z))).mpr
  linarith

/-- The exact arithmetic operator is bounded by a contracting constant and
three explicit powers of the reciprocal logarithmic error. -/
theorem operator_exponential_polynomial_le (T z : ℝ) (hz : 64 ≤ z)
    (hT : z^2 ≤ T) :
    SieveStoppingTwoStep.operator exponential T z ≤ exponential T z *
      (99/100 + exp 2*((35/2)*epsilon z+(535/4)*(epsilon z)^2+
        (1173/4)*(epsilon z)^3)) := by
  have hz2 : 2 ≤ z := by linarith
  have hA : 0 < log T := log_pos (by nlinarith)
  have hr := parameter_ge_two T z hz2 hT
  have he := epsilon_nonneg z hz2
  have hJ : innerSum (log T) z ≤ exp (-(log T/log z)) *
      (99/100+(5/2)*exp 2*epsilon z) := by
    simpa only [innerSum, RosserInnerCalculus.test,
      PrimeEulerLogSubstitution.parameter, epsilon] using
      PrimeEulerRosserInnerBound.prime_inner_sum_le (log T) z hA hz2 hr
  have h1 := weightedMoment_one_le (log T) z hA hz2 hr
  have h2 := weightedMoment_two_le (log T) z hA hz2 hr
  have hexp : exp (1-log T/log z) = exp 1*exp (-(log T/log z)) := by
    rw [← exp_add]
    congr 1
  have he2 : exp 2 = exp 1*exp 1 := by rw [← exp_add]; norm_num
  calc
    _ ≤ innerSum (log T) z + (20*exp 1*epsilon z)*weightedMoment (log T) z 1 +
        (51*exp 1*(epsilon z)^2)*weightedMoment (log T) z 2 :=
      operator_le_prime_sums T z hz2 hT
    _ ≤ exp (-(log T/log z))*(99/100+(5/2)*exp 2*epsilon z) +
        (20*exp 1*epsilon z)*(exp (1-log T/log z)*(3/4+(7/2)*epsilon z)) +
        (51*exp 1*(epsilon z)^2)*(exp (1-log T/log z)*(5/4+(23/4)*epsilon z)) :=
      add_le_add (add_le_add hJ (mul_le_mul_of_nonneg_left h1 (by positivity)))
        (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by rw [hexp, he2]; unfold exponential; ring

/-- Actual two-step arithmetic contraction; no continuous comparison or prime
density estimate remains as a hypothesis. -/
theorem operator_exponential_le (T z : ℝ) (hz : 64 ≤ z) (hT : z^2 ≤ T)
    (hlog : 100000*PrimeEulerDimensionOne.errorConstant ≤ log z) :
    SieveStoppingTwoStep.operator (fun T z => exp (-(log T/log z))) T z ≤
      (199/200)*exp (-(log T/log z)) := by
  have hz2 : 2 ≤ z := by linarith
  have hh := operator_exponential_polynomial_le T z hz hT
  have hb := scalar_budget (epsilon z) (epsilon_nonneg z hz2) (epsilon_small z hz2 hlog)
  calc
    _ ≤ exponential T z*(99/100 + exp 2*((35/2)*epsilon z+
        (535/4)*(epsilon z)^2+(1173/4)*(epsilon z)^3)) := hh
    _ ≤ exponential T z*(199/200) :=
      mul_le_mul_of_nonneg_left hb (exp_pos _).le
    _ = _ := by unfold exponential; ring

run_cmd do
  for decl in [``epsilon_nonneg, ``operator_factorization, ``child_parameter,
      ``epsilon_rescale, ``parameter_ge_two, ``operator_le_prime_sums,
      ``weightedMoment_one_le, ``weightedMoment_two_le, ``scalar_budget, ``epsilon_small,
      ``operator_exponential_polynomial_le, ``operator_exponential_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL TWO-STEP ARITHMETIC CONTRACTION: STANDARD AXIOMS ONLY"

end SieveStoppingArithmeticContraction
end
