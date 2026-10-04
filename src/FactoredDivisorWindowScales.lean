import PolynomialLogEnvelope

/-! Actual source-window scale guards, independently of the analytic region. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter
namespace FactoredDivisorVariableWindow

def sourceWindow (s X : ℝ) : ℝ := (1 / 2) * X ^ (1 / 10 + s)

theorem eventual_source_window_guards (s : ℝ) (hs : 0 < s)
    (hsmall : s < 1 / 100) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      X ^ (1 / 10 + s / 2) ≤ sourceWindow s X ∧
      sourceWindow s X ≤ X / 2 := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound
    2 (s / 2) (by norm_num) (by positivity)] with X htwo
  have hXp : 0 < X := by linarith [htwo.1]
  have hproduct : 2 * X ^ (1 / 10 + s / 2) ≤ X ^ (1 / 10 + s) := by
    calc
      _ ≤ X ^ (s / 2) * X ^ (1 / 10 + s / 2) :=
        mul_le_mul_of_nonneg_right htwo.2 (by positivity)
      _ = X ^ (1 / 10 + s) := by
        rw [← Real.rpow_add hXp]
        congr 1
        ring
  have hupper : X ^ (1 / 10 + s) ≤ X := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le htwo.1
        (by linarith : 1 / 10 + s ≤ (1 : ℝ))
  refine ⟨htwo.1, ?_, ?_⟩ <;> dsimp [sourceWindow] <;> linarith

end FactoredDivisorVariableWindow

#print axioms FactoredDivisorVariableWindow.eventual_source_window_guards
run_cmd do
  let axioms ← Lean.collectAxioms
    ``FactoredDivisorVariableWindow.eventual_source_window_guards
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FACTORED DIVISOR SOURCE WINDOW SCALES PASSED"
