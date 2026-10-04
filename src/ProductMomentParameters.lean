import NormalizedProductMeanSquare
import EighthMomentParameters

/-!
Explicit coefficients for the fractional moment of a mixed product.
This follows EighthMomentParameters, using the actual two-factor energy.
The product length Q can be as large as X squared.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace ProductMomentParameters
open DyadicLevelParameters

def energy (D : ℝ) (Q : ℕ) (α β X : ℝ) : ℝ :=
  D * (4 * (Q : ℝ)) ^ α * X ^ β / Q

def meanSquare (C : ℝ) (Q : ℕ) (T α β X : ℝ) : ℝ :=
  (T + 16 * Q * (1 + Real.log (4 * Q))) * energy C Q α β X

def quadraticConstant : ℝ := 516 * 2 ^ 3 * 4
def sexticConstant : ℝ := 516 * 1024 ^ 2 * 2 ^ 7 * 4

theorem energy_eq (D : ℝ) (K M : ℕ) (α β X : ℝ)
    (hK : 1 ≤ K) (hM : 1 ≤ M) :
    NormalizedProductLevel.energyBudget D K M α 1 (X ^ β) =
      energy D (K * M) α β X := by
  have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  unfold NormalizedProductLevel.energyBudget energy
  push_cast
  rw [mul_assoc (4 : ℝ) (K : ℝ) (M : ℝ)]
  field_simp

theorem quadratic_eq (D : ℝ) (Q : ℕ) (T α β X : ℝ) (hQ : 1 ≤ Q) :
    quadratic Q 2 T (energy D Q α β X) =
      quadraticConstant * D * (4 * (Q : ℝ)) ^ α * X ^ β *
        (1 + Real.log (T + 1)) := by
  have hQp : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  unfold quadratic energy quadraticConstant
  push_cast
  field_simp

theorem sextic_eq (D : ℝ) (Q : ℕ) (T α β X : ℝ) (hQ : 1 ≤ Q) :
    sextic Q 2 T (energy D Q α β X) =
      sexticConstant * D ^ 3 * ((4 * (Q : ℝ)) ^ α) ^ 3 *
        (X ^ β) ^ 3 * (1 + Real.log (T + 1)) *
          (1 + Real.log (4 * (Q : ℝ) + 1)) * T / (Q : ℝ) ^ 2 := by
  have hQp : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  unfold sextic energy sexticConstant
  push_cast
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
  field_simp
  ring

theorem log_bounds (Q T X : ℝ) (hQ : 1 ≤ Q) (hQX : Q ≤ X ^ 2)
    (hX : 1 ≤ X) (hT : 1 ≤ T) (hTX : T ≤ X) :
    1 ≤ 1 + Real.log X ∧
      1 + Real.log (4 * Q) ≤ 3 * (1 + Real.log X) ∧
      1 + Real.log (T + 1) ≤ 2 * (1 + Real.log X) ∧
      1 + Real.log (4 * Q + 1) ≤ 4 * (1 + Real.log X) := by
  have hXp : 0 < X := by linarith
  have hQp : 0 < Q := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hl2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlog2X : Real.log (2 * X) ≤ 1 + Real.log X := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXp.ne']
    linarith
  have hlogQ : Real.log (4 * Q) ≤ 2 * (1 + Real.log X) := by
    have hh := Real.log_le_log (by positivity : 0 < 4 * Q)
      (show 4 * Q ≤ (2 * X) ^ 2 by nlinarith)
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hX23 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hX (by norm_num)
  have hX3 : 1 ≤ X ^ 3 := one_le_pow₀ hX
  have hlogQ1 : Real.log (4 * Q + 1) ≤ 3 * (1 + Real.log X) := by
    have hh := Real.log_le_log (by positivity : 0 < 4 * Q + 1)
      (show 4 * Q + 1 ≤ (2 * X) ^ 3 by nlinarith)
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hlogT : Real.log (T + 1) ≤ 1 + Real.log X :=
    (Real.log_le_log (by linarith : 0 < T + 1)
      (show T + 1 ≤ 2 * X by linarith)).trans hlog2X
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end ProductMomentParameters

#print axioms ProductMomentParameters.log_bounds
run_cmd do
  for target in [``ProductMomentParameters.energy_eq,
      ``ProductMomentParameters.quadratic_eq,
      ``ProductMomentParameters.sextic_eq,
      ``ProductMomentParameters.log_bounds] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "PRODUCT MOMENT PARAMETERS PASSED"
