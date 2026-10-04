import SieveStoppingSharpContraction
import RosserKernelSharper

/-! Improved unconditional contraction of the actual finite stopping operator.
The arithmetic error is retained separately for use at a fixed ratio. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real
namespace SieveStoppingSharpOperator
open SieveStoppingArithmeticContraction SieveStoppingSharpContraction

theorem error_budget (e : ℝ) (he : 0 ≤ e) (hemax : e ≤ 1/100000) :
    exp 2*((35/2)*e+(535/4)*e^2+(1173/4)*e^3) ≤ (1/500:ℝ) := by
  have h2 : e^2 ≤ (1/100000:ℝ)^2 := pow_le_pow_left₀ he hemax 2
  have h3 : e^3 ≤ (1/100000:ℝ)^3 := pow_le_pow_left₀ he hemax 3
  have hp : (35/2)*e+(535/4)*e^2+(1173/4)*e^3 ≤
      (35/2)*(1/100000:ℝ)+(535/4)*(1/100000:ℝ)^2+(1173/4)*(1/100000:ℝ)^3 := by
    nlinarith
  have hp0 : 0 ≤ (35/2)*e+(535/4)*e^2+(1173/4)*e^3 := by positivity
  exact (mul_le_mul RosserKernelContraction.exp_two_le hp hp0 (by norm_num)).trans (by norm_num)

theorem operator_exponential_majorant_small (T z : ℝ) (hz : 64 ≤ z)
    (hT : z^2 ≤ T) (hlog : 100000*PrimeEulerDimensionOne.errorConstant ≤ log z) :
    SieveStoppingTwoStep.operator (fun T z => exp (-(log T/log z))) T z ≤
      exp (-(log T/log z))*(RosserKernelContraction.majorant (log T/log z)+1/500) := by
  have hh := operator_exponential_majorant T z hz hT
  have he := error_budget (epsilon z) (epsilon_nonneg z (by linarith))
    (epsilon_small z (by linarith) hlog)
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl he) (exp_pos _).le)

theorem operator_exponential_le (T z : ℝ) (hz : 64 ≤ z) (hT : z^2 ≤ T)
    (hlog : 100000*PrimeEulerDimensionOne.errorConstant ≤ log z) :
    SieveStoppingTwoStep.operator (fun T z => exp (-(log T/log z))) T z ≤
      (5/6)*exp (-(log T/log z)) := by
  have hm := RosserKernelSharper.majorant_le (log T/log z)
    (parameter_ge_two T z (by linarith) hT)
  have hb : RosserKernelContraction.majorant (log T/log z)+1/500 ≤ (5/6:ℝ) := by
    linarith
  calc
    _ ≤ exp (-(log T/log z))*(RosserKernelContraction.majorant (log T/log z)+1/500) :=
      operator_exponential_majorant_small T z hz hT hlog
    _ ≤ exp (-(log T/log z))*(5/6) := mul_le_mul_of_nonneg_left hb (exp_pos _).le
    _ = _ := mul_comm _ _

run_cmd do
  for decl in [``error_budget, ``operator_exponential_majorant_small,
    ``operator_exponential_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL STOPPING OPERATOR CONTRACTION AT MOST 5/6 PASSED"
end SieveStoppingSharpOperator
end
