import PrimeEulerExponentialCalculus
import PrimeEulerWeightedTransfer

/-! Actual finite prime-Euler sums of the exponential test, with the endpoint
and logarithmic-density errors retained. The arithmetic input is the proved
weighted transfer theorem, not an assumed prime density. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators

namespace PrimeEulerExponentialBound
open PrimeEulerExponentialCalculus PrimeEulerWeightedTransfer PrimeEulerLogBounds
open SieveStoppingExpansion

def derivative (A x : ℝ) : ℝ := A * logKernel A 2 x

theorem test_hasDerivAt (A x : ℝ) (hx : 1 < x) :
    HasDerivAt (test A) (derivative A x) x := by
  convert! PrimeEulerExponentialCalculus.test_hasDerivAt A x hx using 1
  unfold derivative logKernel
  ring

theorem derivative_continuousOn (A a b : ℝ) (ha : 1 < a) :
    ContinuousOn (derivative A) (Icc a b) :=
  (logKernel_continuousOn A a b 2 ha).const_mul A

theorem derivative_nonneg (A x : ℝ) (hA : 0 ≤ A) (hx : 1 < x) :
    0 ≤ derivative A x := mul_nonneg hA (logKernel_nonneg A x 2 hx)

theorem integral_density_bound (A a b : ℝ) (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, test A t * tailDensity t b) ≤
      log b*(test A b/A) + (2*PrimeEulerDimensionOne.errorConstant*log b)*moment A b := by
  have hlb : 0 ≤ log b := (log_pos (by linarith : 1 < b)).le
  have hK : 0 ≤ PrimeEulerDimensionOne.errorConstant :=
    PrimeEulerDimensionOne.errorConstant_pos.le
  have hcoef : 0 ≤ 2*PrimeEulerDimensionOne.errorConstant*log b := by positivity
  have hi2 := logKernel_intervalIntegrable A a b 2 ha hab
  have hi3 := logKernel_intervalIntegrable A a b 3 ha hab
  have heq : (fun t => test A t*tailDensity t b) =
      (fun t => log b*logKernel A 2 t +
        (2*PrimeEulerDimensionOne.errorConstant*log b)*logKernel A 3 t) := by
    funext t
    unfold tailDensity logKernel
    ring
  rw [heq, intervalIntegral.integral_add (hi2.const_mul _) (hi3.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (integral_log_sq_le A a b hA ha hab) hlb)
    (mul_le_mul_of_nonneg_left (integral_log_cube_le A a b hA ha hab) hcoef)

theorem interval_sum_bound (A a b : ℝ) (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ intervalPrimes a b, test A p *
      (PrimeEulerMass.weight p / primeEuler b)) ≤
      test A b*(PrimeEulerDimensionOne.errorConstant/log b) +
        log b*(test A b/A) +
          (2*PrimeEulerDimensionOne.errorConstant*log b)*moment A b := by
  have hh := prime_weighted_transfer_density (test A) (derivative A) a b ha hab
    (test_pos A a).le (test_continuousOn A a b (by linarith))
    (derivative_continuousOn A a b (by linarith))
    (fun x hx => derivative_nonneg A x hA.le (by linarith [hx.1]))
    (fun x hx => test_hasDerivAt A x (by linarith [hx.1]))
  exact hh.trans (by linarith [integral_density_bound A a b hA ha hab])

theorem parameter_identity (A b : ℝ) (hA : 0 < A) (hb : 1 < b) :
    test A b*(PrimeEulerDimensionOne.errorConstant/log b) +
        log b*(test A b/A) +
          (2*PrimeEulerDimensionOne.errorConstant*log b)*moment A b =
      exp (1-A/log b)*(1/(A/log b) +
        (PrimeEulerDimensionOne.errorConstant/log b)*(1+2*(A/log b+1)/(A/log b)^2)) := by
  have hAn : A ≠ 0 := ne_of_gt hA
  have hbn : log b ≠ 0 := ne_of_gt (log_pos hb)
  unfold moment test
  field_simp
  ring

theorem interval_exponential_sum_le (A a b : ℝ)
    (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ intervalPrimes a b, test A p *
      (PrimeEulerMass.weight p / primeEuler b)) ≤
      exp (1-A/log b)*(1/(A/log b) +
        (PrimeEulerDimensionOne.errorConstant/log b)*(1+2*(A/log b+1)/(A/log b)^2)) :=
  (interval_sum_bound A a b hA ha hab).trans_eq
    (parameter_identity A b hA (by linarith))

theorem intervalPrimes_two_eq_pool (b : ℝ) : intervalPrimes 2 b = SieveSmallWeights.pool b := by
  ext p
  rw [mem_intervalPrimes, SieveSmallWeights.mem_pool]
  constructor
  · exact fun hp => ⟨hp.1, hp.2.1⟩
  · intro hp
    exact ⟨hp.1, hp.2, by exact_mod_cast hp.1.two_le⟩

theorem prime_exponential_sum_le (A b : ℝ) (hA : 0 < A) (hb : 2 ≤ b) :
    (∑ p ∈ SieveSmallWeights.pool b, test A p *
      (PrimeEulerMass.weight p / primeEuler b)) ≤
      exp (1-A/log b)*(1/(A/log b) +
        (PrimeEulerDimensionOne.errorConstant/log b)*(1+2*(A/log b+1)/(A/log b)^2)) := by
  simpa only [intervalPrimes_two_eq_pool] using
    interval_exponential_sum_le A 2 b hA (by norm_num) hb

run_cmd do
  for decl in [``test_hasDerivAt, ``derivative_continuousOn, ``derivative_nonneg,
      ``integral_density_bound, ``interval_sum_bound, ``parameter_identity,
      ``interval_exponential_sum_le, ``intervalPrimes_two_eq_pool,
      ``prime_exponential_sum_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL PRIME EULER EXPONENTIAL BOUND: STANDARD AXIOMS ONLY"

end PrimeEulerExponentialBound
end
