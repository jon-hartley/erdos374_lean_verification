import PrimeEulerHarmonicNormalization

/-! Normalize the proposed positive contribution using the actual proved
Euler-product upper bound. This compares its scale; it does not establish
any positive three-prime counting estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real Filter
namespace SievePositiveScale
open SieveStoppingExpansion

def exponent (s : ℝ) : ℝ := (26/105)*(1-3*s)

theorem exponent_pos (s : ℝ) (hs : s < 1/3) : 0 < exponent s := by
  unfold exponent
  linarith

theorem coefficient_comparison (X s : ℝ) (hX : 1 < X)
    (hV : primeEuler (X^exponent s)*log (X^exponent s) ≤ (5/8:ℝ)) :
    ((104/1875)*(1-3*s))*primeEuler (X^exponent s) ≤ (7/50)/log X := by
  rw [log_rpow (by linarith : 0 < X)] at hV
  apply (le_div_iff₀ (log_pos hX)).mpr
  have hid : (((104/1875)*(1-3*s))*primeEuler (X^exponent s))*log X =
      (28/125)*(primeEuler (X^exponent s)*(exponent s*log X)) := by
    unfold exponent
    ring
  rw [hid]
  exact (mul_le_mul_of_nonneg_left hV (by norm_num : (0:ℝ) ≤ 28/125)).trans_eq
    (by norm_num)

theorem eventually_coefficient_comparison (s : ℝ) (hs : s < 1/3) :
    ∃ X₀ : ℝ, 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ((104/1875)*(1-3*s))*primeEuler (X^exponent s) ≤ (7/50)/log X := by
  have he := (tendsto_rpow_atTop (exponent_pos s hs)).eventually
    PrimeEulerHarmonicNormalization.eventually_product_log_bound
  obtain ⟨A, hA⟩ := eventually_atTop.mp he
  refine ⟨max 2 A, lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_left _ _), ?_⟩
  intro X hX
  have hX1 : 1 < X := lt_of_lt_of_le (by norm_num : (1:ℝ) < 2)
    ((le_max_left _ _).trans hX)
  exact coefficient_comparison X s hX1 (hA X ((le_max_right _ _).trans hX))

run_cmd do
  for decl in [``exponent_pos, ``coefficient_comparison, ``eventually_coefficient_comparison] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "POSITIVE CONTRIBUTION SCALE NORMALIZED; THREE-PRIME ESTIMATE REMAINS OPEN"
end SievePositiveScale
end
