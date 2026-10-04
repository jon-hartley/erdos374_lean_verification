import PowerDifferenceParameters

/-!
Real ambient-scale bounds that absorb fixed logarithmic factors into an
arbitrarily small positive power. Constants are fixed before the scale.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Filter

namespace PolynomialLogEnvelope

theorem eventually_bound (C : ℝ) (m : ℕ) (δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ C * (1 + Real.log X) ^ m ≤ X ^ δ := by
  have hlimit : Tendsto
      (fun X : ℝ => (C * (2 : ℝ) ^ m) * Real.log X ^ m / X ^ δ) atTop (nhds 0) := by
    simpa only [Real.rpow_natCast, mul_zero, mul_div_assoc] using
      (Real.tendsto_pow_log_div_pow_atTop δ m hδ).const_mul (C * (2 : ℝ) ^ m)
  have hsmall := hlimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlarge := Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hsmall, hlarge, eventually_ge_atTop (1 : ℝ)] with X hsmall hlog hX
  have hXp : 0 < X := by linarith
  refine ⟨hX, ?_⟩
  have hh := ((div_lt_one (Real.rpow_pos_of_pos hXp δ)).mp hsmall).le
  calc
    _ ≤ C * (2 * Real.log X) ^ m := by gcongr; linarith
    _ = (C * (2 : ℝ) ^ m) * Real.log X ^ m := by rw [mul_pow]; ring
    _ ≤ _ := hh

theorem eventually_constant_bound (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ C ≤ X ^ δ := by
  simpa only [pow_zero, mul_one] using eventually_bound C 0 δ hC hδ

end PolynomialLogEnvelope

#print axioms PolynomialLogEnvelope.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``PolynomialLogEnvelope.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "POLYNOMIAL LOG ENVELOPE PASSED"
