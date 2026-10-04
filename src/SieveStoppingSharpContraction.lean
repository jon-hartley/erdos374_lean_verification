import SieveStoppingArithmeticContraction

/-! Preserve the pointwise continuous kernel majorant through the actual
prime transfer and every arithmetic error term. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
open Real Set MeasureTheory
namespace SieveStoppingSharpContraction
open RosserInnerIntegral PrimeEulerLogSubstitution PrimeEulerWeightedTransfer
open SieveStoppingExpansion PrimeEulerRosserInnerBound SieveStoppingArithmeticContraction

theorem inner_majorant (r : ℝ) (hr : 2 ≤ r) :
    (1/r)*(∫ s in Ioi (r-1), inner s) ≤
      RosserKernelContraction.majorant r*exp (-r) := by
  have h := weighted_inner_le_majorant r hr
  have he : exp (-r)*exp r = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  have hh := mul_le_mul_of_nonneg_left h (exp_pos (-r)).le
  calc
    _ = exp (-r)*(exp r/r*(∫ s in Ioi (r-1), inner s)) := by
      rw [show exp (-r)*(exp r/r*(∫ s in Ioi (r-1), inner s)) =
        (exp (-r)*exp r)/r*(∫ s in Ioi (r-1), inner s) by ring, he]
    _ ≤ exp (-r)*RosserKernelContraction.majorant r := hh
    _ = _ := by ring

theorem leading_integral_majorant (A a b : ℝ) (hA : 0 < A)
    (ha : 2 ≤ a) (hab : a ≤ b) (hr : 2 ≤ A/log b) :
    log b * (∫ x in a..b, kernel A 2 x) ≤ (RosserKernelContraction.majorant (A/log b))*exp (-(A/log b)) := by
  have hb : 0 < log b := log_pos (by linarith)
  have hp : 1 ≤ parameter A b := by unfold parameter; linarith
  have he := parameter_endpoints A a b hA.le (by linarith) hab
  have hfin := finite_inner_integral_le (parameter A b) (parameter A a) hp he
  have hsub : (∫ x in a..b, kernel A 2 x) =
      (∫ s in parameter A b..parameter A a, inner s)/A := by
    simpa [kernel, RosserInnerCalculus.test] using
      integral_substitution inner A a b 0 hA (by linarith) hab
  rw [hsub]
  calc
    _ ≤ log b * ((∫ s in Ioi (parameter A b), inner s)/A) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hfin hA.le) hb.le
    _ = (1/(A/log b)) * (∫ s in Ioi (parameter A b), inner s) := by
      field_simp
    _ ≤ _ := by simpa only [parameter] using inner_majorant (A/log b) hr

/-- Actual outer first-prime sum of J, including its endpoint and moment errors. -/
theorem prime_inner_sum_majorant (A b : ℝ) (hA : 0 < A) (hb : 2 ≤ b)
    (hr : 2 ≤ A/log b) :
    (∑ p ∈ SieveSmallWeights.pool b, RosserInnerCalculus.test A p *
      (PrimeEulerMass.weight p / primeEuler b)) ≤
      exp (-(A/log b)) * (RosserKernelContraction.majorant (A/log b) +
        (5/2)*exp 2*(PrimeEulerDimensionOne.errorConstant/log b)) := by
  have hp : ∀ x ∈ Icc 2 b, 1 ≤ parameter A x :=
    fun x hx => RosserInnerCalculus.parameter_ge_one A 2 b x hA (by norm_num) hr hx
  have hh := PrimeEulerRightTransfer.prime_weighted_transfer_density_right
    (RosserInnerCalculus.test A) (RosserInnerCalculus.derivative A) 2 b (by norm_num) hb
    (inner_nonneg _ (hp 2 ⟨le_rfl, hb⟩))
    (RosserInnerCalculus.test_continuousOn A 2 b hA (by norm_num) hr)
    (RosserInnerCalculus.derivative_intervalIntegrable A 2 b hA (by norm_num) hb hr)
    (fun x hx => RosserInnerCalculus.derivative_nonneg A x hA (by linarith [hx.1]) (hp x hx))
    (fun x hx => RosserInnerCalculus.test_hasDeriv_right A x hA (by linarith [hx.1])
      (hp x ⟨hx.1.le, hx.2.le⟩))
  rw [PrimeEulerExponentialBound.intervalPrimes_two_eq_pool,
    density_integral_eq A 2 b hA (by norm_num) hb hr] at hh
  have h0 := endpoint_bound A b hb hr
  have h1 := leading_integral_majorant A 2 b hA (by norm_num) hb hr
  have h2 := moment_integral_bound A 2 b hA (by norm_num) hb hr
  calc
    _ ≤ RosserInnerCalculus.test A b*(PrimeEulerDimensionOne.errorConstant/log b) +
        (log b*(∫ x in (2:ℝ)..b, kernel A 2 x) +
          (2*PrimeEulerDimensionOne.errorConstant*log b)*(∫ x in (2:ℝ)..b, kernel A 3 x)) := hh
    _ ≤ exp 2*(PrimeEulerDimensionOne.errorConstant/log b)*exp (-(A/log b)) +
        (RosserKernelContraction.majorant (A/log b)*exp (-(A/log b)) +
          (3/2)*exp 2*(PrimeEulerDimensionOne.errorConstant/log b)*exp (-(A/log b))) :=
      add_le_add h0 (add_le_add h1 h2)
    _ = _ := by ring

/-- The exact arithmetic operator is bounded by a contracting constant and
three explicit powers of the reciprocal logarithmic error. -/
theorem operator_exponential_majorant (T z : ℝ) (hz : 64 ≤ z)
    (hT : z^2 ≤ T) :
    SieveStoppingTwoStep.operator exponential T z ≤ exponential T z *
      (RosserKernelContraction.majorant (log T/log z) + exp 2*((35/2)*epsilon z+(535/4)*(epsilon z)^2+
        (1173/4)*(epsilon z)^3)) := by
  have hz2 : 2 ≤ z := by linarith
  have hA : 0 < log T := log_pos (by nlinarith)
  have hr := parameter_ge_two T z hz2 hT
  have he := epsilon_nonneg z hz2
  have hJ : innerSum (log T) z ≤ exp (-(log T/log z)) *
      (RosserKernelContraction.majorant (log T/log z)+(5/2)*exp 2*epsilon z) := by
    simpa only [innerSum, RosserInnerCalculus.test,
      PrimeEulerLogSubstitution.parameter, epsilon] using
      prime_inner_sum_majorant (log T) z hA hz2 hr
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
    _ ≤ exp (-(log T/log z))*(RosserKernelContraction.majorant (log T/log z)+(5/2)*exp 2*epsilon z) +
        (20*exp 1*epsilon z)*(exp (1-log T/log z)*(3/4+(7/2)*epsilon z)) +
        (51*exp 1*(epsilon z)^2)*(exp (1-log T/log z)*(5/4+(23/4)*epsilon z)) :=
      add_le_add (add_le_add hJ (mul_le_mul_of_nonneg_left h1 (by positivity)))
        (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by rw [hexp, he2]; unfold exponential; ring

run_cmd do
  for decl in [``inner_majorant, ``leading_integral_majorant,
    ``prime_inner_sum_majorant, ``operator_exponential_majorant] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL OPERATOR RETAINS POINTWISE KERNEL MAJORANT AND ARITHMETIC ERRORS"
end SieveStoppingSharpContraction
end
