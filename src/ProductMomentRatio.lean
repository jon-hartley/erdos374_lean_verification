import NormalizedPowerMoment

/-!
The length ratios for a 5/2 moment of a mixed product. The exact condition
T^8 Z^9 <= Q^9 represents Q >= Z*T^(8/9). This module follows the
existing EighthMomentRatio proof with the mixed-product exponents.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace ProductMomentRatio

theorem bound (Q T Z : ℝ) (hZ : 1 ≤ Z) (hQZ : Z ≤ Q) (hT : 1 ≤ T)
    (hrange : T ^ 8 * Z ^ 9 ≤ Q ^ 9) :
    (T / Q ^ 2) ^ (1 / 7 : ℝ) * (1 + T / Q) ≤
      2 / Z ^ (2 / 7 : ℝ) := by
  have hZp : 0 < Z := by linarith
  have hQp : 0 < Q := by linarith
  have hTp : 0 < T := by linarith
  have hfirst : T * Z ^ 2 ≤ Q ^ 2 := by
    apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ T * Z ^ 2)
      (by positivity : 0 ≤ Q ^ 2) (by norm_num : (9 : ℕ) ≠ 0)).mp
    have hTpow : T ^ 9 ≤ T ^ 16 := pow_le_pow_right₀ hT (by norm_num)
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ T ^ 8 * Z ^ 9) hrange 2
    calc
      _ = T ^ 9 * Z ^ 18 := by ring
      _ ≤ T ^ 16 * Z ^ 18 := mul_le_mul_of_nonneg_right hTpow (by positivity)
      _ = (T ^ 8 * Z ^ 9) ^ 2 := by ring
      _ ≤ (Q ^ 9) ^ 2 := hh
      _ = _ := by ring
  have hsecond : T ^ 8 * Z ^ 2 ≤ Q ^ 9 := by
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hZ (by norm_num : 2 ≤ 9)) (by positivity)).trans hrange
  let R := (T / Q ^ 2) ^ (1 / 7 : ℝ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hR7 : R ^ 7 = T / Q ^ 2 := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ T / Q ^ 2)]
    norm_num
  have hZ7 : (Z ^ (2 / 7 : ℝ)) ^ (7 : ℕ) = Z ^ (2 : ℕ) := by
    rw [← Real.rpow_mul_natCast hZp.le]
    norm_num
  have hsmall : R ≤ 1 / Z ^ (2 / 7 : ℝ) := by
    apply (pow_le_pow_iff_left₀ hR (by positivity : 0 ≤ 1 / Z ^ (2 / 7 : ℝ))
      (by norm_num : (7 : ℕ) ≠ 0)).mp
    rw [hR7, div_pow, one_pow, hZ7]
    exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hfirst)
  have hlarge : R * (T / Q) ≤ 1 / Z ^ (2 / 7 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ R * (T / Q))
      (by positivity : 0 ≤ 1 / Z ^ (2 / 7 : ℝ)) (by norm_num : (7 : ℕ) ≠ 0)).mp
    rw [mul_pow, hR7, div_pow, div_pow, one_pow, hZ7]
    apply (le_div_iff₀ (by positivity : 0 < Z ^ 2)).mpr
    calc
      (T / Q ^ 2 * (T ^ 7 / Q ^ 7)) * Z ^ 2 = (T ^ 8 * Z ^ 2) / Q ^ 9 := by
        field_simp
      _ ≤ 1 := (div_le_one (by positivity)).mpr hsecond
  change R * (1 + T / Q) ≤ 2 / Z ^ (2 / 7 : ℝ)
  calc
    _ = R + R * (T / Q) := by ring
    _ ≤ 1 / Z ^ (2 / 7 : ℝ) + 1 / Z ^ (2 / 7 : ℝ) := add_le_add hsmall hlarge
    _ = _ := by ring

end ProductMomentRatio

#print axioms ProductMomentRatio.bound
run_cmd do
  let axioms ← Lean.collectAxioms ``ProductMomentRatio.bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "PRODUCT MOMENT RATIO PASSED"
