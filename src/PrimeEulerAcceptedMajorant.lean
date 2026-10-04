import PrimeEulerAcceptedParameters
import RosserInnerIntegral

/-! The accepted-prime error is bounded by two smooth exponential moment
tests. No monotonicity or differentiability of the piecewise coefficients is
needed for the subsequent outer prime-measure comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open Real Set

namespace PrimeEulerAcceptedMajorant
open PrimeEulerAcceptedParameters PrimeEulerAcceptedInner

def coefficientA (s : ℝ) : ℝ :=
  if s ≤ 3 then 20*exp (-2)/s^2 else exp (1-s)*(1+3/s+2/s^2)

def coefficientB (s : ℝ) : ℝ :=
  if s ≤ 3 then 51*exp (-2)/s^3 else exp (1-s)*(1+2/s+2/s^2)

theorem exp_one_sub (s : ℝ) : exp (1-s) = exp 1 * exp (-s) := by
  rw [← exp_add]
  congr 1

theorem upperEnvelope_low (s k : ℝ) (hs : 1 ≤ s) (hs3 : s ≤ 3) :
    upperEnvelope s k = exp (-2)/s +
      (20*exp (-2)/s^2)*k + (51*exp (-2)/s^3)*k^2 := by
  have hs0 : s ≠ 0 := by linarith
  have hb : beta s = s/3 := min_eq_right (by linarith)
  have hm : terminalParameter s = 2 := max_eq_left (by linarith)
  unfold upperEnvelope
  rw [hb, hm]
  field_simp
  ring

theorem upperEnvelope_high (s k : ℝ) (hs3 : 3 ≤ s) :
    upperEnvelope s k = exp (1-s)/s +
      (exp (1-s)*(1+3/s+2/s^2))*k +
        (exp (1-s)*(1+2/s+2/s^2))*k^2 := by
  have hs0 : s ≠ 0 := by linarith
  have hb : beta s = 1 := min_eq_left (by linarith)
  have hm : terminalParameter s = s-1 := max_eq_right (by linarith)
  unfold upperEnvelope
  rw [hb, hm, show -(s-1) = 1-s by ring]
  field_simp
  ring

theorem upperEnvelope_expansion (s k : ℝ) (hs : 1 ≤ s) :
    upperEnvelope s k = RosserInnerIntegral.inner s +
      coefficientA s*k + coefficientB s*k^2 := by
  by_cases hs3 : s ≤ 3
  · rw [upperEnvelope_low s k hs hs3, coefficientA, coefficientB,
      ite_eq_left hs3, ite_eq_left hs3, RosserInnerIntegral.inner,
      max_eq_left (by linarith)]
  · rw [upperEnvelope_high s k (by linarith), coefficientA, coefficientB,
      ite_eq_right hs3, ite_eq_right hs3, RosserInnerIntegral.inner,
      max_eq_right (by linarith), show -(s-1) = 1-s by ring]

theorem coefficientA_le (s : ℝ) (hs : 1 ≤ s) :
    coefficientA s ≤ 20*exp 1*exp (-s) := by
  have hs2 : 1 ≤ s^2 := one_le_pow₀ hs
  unfold coefficientA
  split_ifs with hs3
  · have h1 : 20*exp (-2)/s^2 ≤ 20*exp (-2) :=
      div_le_self (by positivity) hs2
    have h2 : exp (-2) ≤ exp (1-s) := exp_le_exp.mpr (by linarith)
    calc
      _ ≤ 20*exp (-2) := h1
      _ ≤ 20*exp (1-s) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = _ := by rw [exp_one_sub]; ring
  · have h1 : 3/s ≤ (3 : ℝ) := div_le_self (by norm_num) hs
    have h2 : 2/s^2 ≤ (2 : ℝ) := div_le_self (by norm_num) hs2
    have hc : 1+3/s+2/s^2 ≤ (20 : ℝ) := by linarith
    calc
      _ ≤ exp (1-s)*20 := mul_le_mul_of_nonneg_left hc (exp_pos _).le
      _ = _ := by rw [exp_one_sub]; ring

theorem coefficientB_le (s : ℝ) (hs : 1 ≤ s) :
    coefficientB s ≤ 51*exp 1*exp (-s) := by
  have hs2 : 1 ≤ s^2 := one_le_pow₀ hs
  have hs3' : 1 ≤ s^3 := one_le_pow₀ hs
  unfold coefficientB
  split_ifs with hs3
  · have h1 : 51*exp (-2)/s^3 ≤ 51*exp (-2) :=
      div_le_self (by positivity) hs3'
    have h2 : exp (-2) ≤ exp (1-s) := exp_le_exp.mpr (by linarith)
    calc
      _ ≤ 51*exp (-2) := h1
      _ ≤ 51*exp (1-s) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = _ := by rw [exp_one_sub]; ring
  · have h1 : 2/s ≤ (2 : ℝ) := div_le_self (by norm_num) hs
    have h2 : 2/s^2 ≤ (2 : ℝ) := div_le_self (by norm_num) hs2
    have hc : 1+2/s+2/s^2 ≤ (51 : ℝ) := by linarith
    calc
      _ ≤ exp (1-s)*51 := mul_le_mul_of_nonneg_left hc (exp_pos _).le
      _ = _ := by rw [exp_one_sub]; ring

/-- Smooth exponential test majorants for the two arithmetic-error terms. -/
theorem upperEnvelope_le (s k : ℝ) (hs : 1 ≤ s) (hk : 0 ≤ k) :
    upperEnvelope s k ≤ RosserInnerIntegral.inner s +
      20*exp 1*k*exp (-s) + 51*exp 1*k^2*exp (-s) := by
  rw [upperEnvelope_expansion s k hs]
  have hA := mul_le_mul_of_nonneg_right (coefficientA_le s hs) hk
  have hB := mul_le_mul_of_nonneg_right (coefficientB_le s hs) (sq_nonneg k)
  calc
    _ ≤ RosserInnerIntegral.inner s + (20*exp 1*exp (-s))*k +
        (51*exp 1*exp (-s))*k^2 := add_le_add (add_le_add (le_refl _) hA) hB
    _ = _ := by ring

/-- The preceding smooth majorant bounds the actual guarded prime sum. -/
theorem accepted_exponential_majorant (T z : ℝ) (hz : 2 ≤ z) (hT : z ≤ T) :
    acceptedExponentialMass T z ≤ RosserInnerIntegral.inner (parameter T z) +
      20*exp 1*(PrimeEulerDimensionOne.errorConstant/log z)*exp (-parameter T z) +
      51*exp 1*(PrimeEulerDimensionOne.errorConstant/log z)^2*exp (-parameter T z) := by
  apply (accepted_exponential_bound T z hz hT).trans
  exact upperEnvelope_le _ _ (parameter_ge_one T z hz hT)
    (div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le
      (log_pos (by linarith : 1 < z)).le)

run_cmd do
  for decl in [``exp_one_sub, ``upperEnvelope_low, ``upperEnvelope_high,
    ``upperEnvelope_expansion, ``coefficientA_le, ``coefficientB_le,
    ``upperEnvelope_le, ``accepted_exponential_majorant] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ACCEPTED-PRIME SMOOTH EXPONENTIAL MAJORANT PASSED"

end PrimeEulerAcceptedMajorant
end
