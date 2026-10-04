import CompactIntegral

/-! Translate a real moment order into the order of a fixed integer power. -/

set_option autoImplicit false
noncomputable section

namespace PowerOrderParameters

theorem bounds (h : ℕ) (beta : ℝ) (hh : 2 ≤ h)
    (hlo : 2 * (h : ℝ) ≤ beta) (hhi : beta ≤ 2 * (h : ℝ) + 2) :
    2 ≤ beta / (h : ℝ) ∧ beta / (h : ℝ) ≤ 3 := by
  have hhr : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hp : (0 : ℝ) < h := by linarith
  exact ⟨(le_div_iff₀ hp).mpr hlo, (div_le_iff₀ hp).mpr (by linarith)⟩

theorem order_identity (h : ℕ) (beta : ℝ) (hh : 1 ≤ h) :
    (h : ℝ) * (beta / (h : ℝ)) = beta := by
  have hp : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  field_simp

theorem length_identity (N : ℝ) (h : ℕ) (beta : ℝ)
    (hN : 0 ≤ N) (hh : 1 ≤ h) :
    (N ^ h) ^ (beta / (h : ℝ) + 2) = N ^ (beta + 2 * h) := by
  rw [← Real.rpow_natCast_mul hN]
  congr 1
  have hid := order_identity h beta hh
  nlinarith

end PowerOrderParameters

#print axioms PowerOrderParameters.length_identity
run_cmd do
  for target in [``PowerOrderParameters.bounds,
      ``PowerOrderParameters.order_identity, ``PowerOrderParameters.length_identity] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "POWER ORDER PARAMETERS PASSED"
