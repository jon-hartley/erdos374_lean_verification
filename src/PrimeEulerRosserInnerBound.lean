import RosserInnerCalculus
import RosserExponentialMoments
import PrimeEulerExponentialBound

/-! Actual-prime transfer of the inner Rosser test. The ideal leading
integral retains its contraction; only the endpoint and first-moment errors
are replaced by exponential bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
open Real Set Filter MeasureTheory

namespace PrimeEulerRosserInnerBound
open RosserInnerIntegral PrimeEulerLogSubstitution
open PrimeEulerWeightedTransfer SieveStoppingExpansion

theorem finite_integral_le_Ioi (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hfi : IntegrableOn f (Ioi a)) (hf : ∀ x ∈ Ioi a, 0 ≤ f x) :
    (∫ x in a..b, f x) ≤ ∫ x in Ioi a, f x := by
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_mono_set hfi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact hf x hx
  · exact Filter.Eventually.of_forall (fun x hx => hx.1)

theorem finite_inner_integral_le (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ s in a..b, inner s) ≤ ∫ s in Ioi a, inner s :=
  finite_integral_le_Ioi inner a b hab (inner_integrable a ha)
    (fun s hs => inner_nonneg s (ha.trans hs.le))

theorem inner_moment_integrable (a : ℝ) (ha : 1 ≤ a) :
    IntegrableOn (fun s => inner s*(s+1)) (Ioi a) := by
  have hc : ContinuousOn (fun s => inner s*(s+1)) (Ioi a) := by
    intro s hs
    exact ((RosserInnerCalculus.inner_continuousAt s (by linarith [hs.out])).mul
      (continuousAt_id.add continuousAt_const)).continuousWithinAt
  apply ((RosserExponentialMoments.moment1_integrable a ha).const_mul (exp 1)).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hs1 : 1 ≤ s := ha.trans hs.le
  have hp : 0 ≤ s+1 := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inner_nonneg s hs1) hp)]
  simpa only [pow_one, mul_assoc] using
    mul_le_mul_of_nonneg_right (inner_le_exp s hs1) hp

theorem inner_moment_integral_le (a : ℝ) (ha : 1 ≤ a) :
    (∫ s in Ioi a, inner s*(s+1)) ≤ exp 1 * (exp (-a)*(a+2)) := by
  have hh := setIntegral_mono_on (inner_moment_integrable a ha)
    ((RosserExponentialMoments.moment1_integrable a ha).const_mul (exp 1))
    measurableSet_Ioi (fun s hs => by
      have hs1 : 1 ≤ s := ha.trans hs.le
      simpa only [pow_one, mul_assoc] using
        mul_le_mul_of_nonneg_right (inner_le_exp s hs1) (by linarith : 0 ≤ s+1))
  rw [integral_const_mul, RosserExponentialMoments.moment1_integral a ha] at hh
  exact hh

theorem finite_inner_moment_le (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ s in a..b, inner s*(s+1)) ≤ exp 1 * (exp (-a)*(a+2)) := by
  apply (finite_integral_le_Ioi (fun s => inner s*(s+1)) a b hab
    (inner_moment_integrable a ha) ?_).trans (inner_moment_integral_le a ha)
  intro s hs
  exact mul_nonneg (inner_nonneg s (ha.trans hs.le)) (by linarith [hs.out])

def kernel (A : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  RosserInnerCalculus.test A x / (x*(log x)^k)

theorem kernel_continuousOn (A a b : ℝ) (k : ℕ) (hA : 0 < A)
    (ha : 1 < a) (hr : 2 ≤ A/log b) :
    ContinuousOn (kernel A k) (Icc a b) := by
  have hn : ∀ x ∈ Icc a b, x ≠ 0 := fun x hx => by linarith [hx.1]
  have hl : ∀ x ∈ Icc a b, log x ≠ 0 := fun x hx =>
    (log_pos (ha.trans_le hx.1)).ne'
  exact (RosserInnerCalculus.test_continuousOn A a b hA ha hr).div
    (continuousOn_id.mul ((continuousOn_id.log hn).pow k))
      (fun x hx => mul_ne_zero (hn x hx) (pow_ne_zero k (hl x hx)))

theorem kernel_intervalIntegrable (A a b : ℝ) (k : ℕ) (hA : 0 < A)
    (ha : 2 ≤ a) (hab : a ≤ b) (hr : 2 ≤ A/log b) :
    IntervalIntegrable (kernel A k) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact (kernel_continuousOn A a b k hA (by linarith) hr).integrableOn_Icc

theorem density_integral_eq (A a b : ℝ) (hA : 0 < A)
    (ha : 2 ≤ a) (hab : a ≤ b) (hr : 2 ≤ A/log b) :
    (∫ x in a..b, RosserInnerCalculus.test A x * tailDensity x b) =
      log b * (∫ x in a..b, kernel A 2 x) +
        (2*PrimeEulerDimensionOne.errorConstant*log b) * (∫ x in a..b, kernel A 3 x) := by
  have h2 := kernel_intervalIntegrable A a b 2 hA ha hab hr
  have h3 := kernel_intervalIntegrable A a b 3 hA ha hab hr
  have heq : (fun x => RosserInnerCalculus.test A x * tailDensity x b) =
      (fun x => log b*kernel A 2 x +
        (2*PrimeEulerDimensionOne.errorConstant*log b)*kernel A 3 x) := by
    funext x
    unfold tailDensity kernel
    ring
  rw [heq, intervalIntegral.integral_add (h2.const_mul _) (h3.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem leading_integral_bound (A a b : ℝ) (hA : 0 < A)
    (ha : 2 ≤ a) (hab : a ≤ b) (hr : 2 ≤ A/log b) :
    log b * (∫ x in a..b, kernel A 2 x) ≤ (99/100)*exp (-(A/log b)) := by
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
    _ ≤ _ := by simpa only [parameter] using inner_contraction (A/log b) hr

theorem exp_parameter_identity (A b : ℝ) :
    exp 1 * exp (-parameter A b) = exp 2 * exp (-(A/log b)) := by
  rw [← exp_add, ← exp_add]
  congr 1
  unfold parameter
  ring

theorem moment_integral_bound (A a b : ℝ) (hA : 0 < A)
    (ha : 2 ≤ a) (hab : a ≤ b) (hr : 2 ≤ A/log b) :
    (2*PrimeEulerDimensionOne.errorConstant*log b) * (∫ x in a..b, kernel A 3 x) ≤
      (3/2)*exp 2*(PrimeEulerDimensionOne.errorConstant/log b)*exp (-(A/log b)) := by
  have hb : 0 < log b := log_pos (by linarith)
  have hK : 0 ≤ PrimeEulerDimensionOne.errorConstant :=
    PrimeEulerDimensionOne.errorConstant_pos.le
  have hp : 1 ≤ parameter A b := by unfold parameter; linarith
  have he := parameter_endpoints A a b hA.le (by linarith) hab
  have hfin := finite_inner_moment_le (parameter A b) (parameter A a) hp he
  have hsub : (∫ x in a..b, kernel A 3 x) =
      (∫ s in parameter A b..parameter A a, inner s*(s+1))/A^2 := by
    simpa [kernel, RosserInnerCalculus.test] using
      integral_substitution inner A a b 1 hA (by linarith) hab
  have hi : (∫ x in a..b, kernel A 3 x) ≤
      exp 2*exp (-(A/log b))*(A/log b+1)/A^2 := by
    rw [hsub]
    apply (div_le_div_of_nonneg_right hfin (sq_nonneg A)).trans_eq
    rw [← mul_assoc, exp_parameter_identity]
    unfold parameter
    ring
  have hm := RosserExponentialMoments.normalized_poly1 (A/log b) hr
  calc
    _ ≤ (2*PrimeEulerDimensionOne.errorConstant*log b) *
        (exp 2*exp (-(A/log b))*(A/log b+1)/A^2) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (2*exp 2*(PrimeEulerDimensionOne.errorConstant/log b)*exp (-(A/log b))) *
        ((A/log b+1)/(A/log b)^2) := by
      field_simp
    _ ≤ (2*exp 2*(PrimeEulerDimensionOne.errorConstant/log b)*exp (-(A/log b)))*(3/4) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

theorem endpoint_bound (A b : ℝ) (hb : 2 ≤ b) (hr : 2 ≤ A/log b) :
    RosserInnerCalculus.test A b*(PrimeEulerDimensionOne.errorConstant/log b) ≤
      exp 2*(PrimeEulerDimensionOne.errorConstant/log b)*exp (-(A/log b)) := by
  have hp : 1 ≤ parameter A b := by unfold parameter; linarith
  have hk : 0 ≤ PrimeEulerDimensionOne.errorConstant/log b :=
    div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le
      (log_pos (by linarith : 1 < b)).le
  calc
    _ ≤ (exp 1*exp (-parameter A b))*(PrimeEulerDimensionOne.errorConstant/log b) :=
      mul_le_mul_of_nonneg_right (inner_le_exp _ hp) hk
    _ = _ := by rw [exp_parameter_identity]; ring

/-- Actual outer first-prime sum of J, including its endpoint and moment errors. -/
theorem prime_inner_sum_le (A b : ℝ) (hA : 0 < A) (hb : 2 ≤ b)
    (hr : 2 ≤ A/log b) :
    (∑ p ∈ SieveSmallWeights.pool b, RosserInnerCalculus.test A p *
      (PrimeEulerMass.weight p / primeEuler b)) ≤
      exp (-(A/log b)) * (99/100 +
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
  have h1 := leading_integral_bound A 2 b hA (by norm_num) hb hr
  have h2 := moment_integral_bound A 2 b hA (by norm_num) hb hr
  calc
    _ ≤ RosserInnerCalculus.test A b*(PrimeEulerDimensionOne.errorConstant/log b) +
        (log b*(∫ x in (2:ℝ)..b, kernel A 2 x) +
          (2*PrimeEulerDimensionOne.errorConstant*log b)*(∫ x in (2:ℝ)..b, kernel A 3 x)) := hh
    _ ≤ exp 2*(PrimeEulerDimensionOne.errorConstant/log b)*exp (-(A/log b)) +
        ((99/100)*exp (-(A/log b)) +
          (3/2)*exp 2*(PrimeEulerDimensionOne.errorConstant/log b)*exp (-(A/log b))) :=
      add_le_add h0 (add_le_add h1 h2)
    _ = _ := by ring

run_cmd do
  for decl in [``finite_integral_le_Ioi, ``finite_inner_integral_le,
    ``inner_moment_integrable, ``inner_moment_integral_le, ``finite_inner_moment_le,
    ``kernel_continuousOn, ``kernel_intervalIntegrable, ``density_integral_eq,
    ``leading_integral_bound, ``exp_parameter_identity, ``moment_integral_bound,
    ``endpoint_bound, ``prime_inner_sum_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL OUTER ROSSER INNER PRIME SUM BOUND PASSED"

end PrimeEulerRosserInnerBound
end
