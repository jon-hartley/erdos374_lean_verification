import NormalizedPowerMoment

/-!
The length threshold behind the eighth-moment saving. The condition
T^2 Z^7 <= N^7 represents N >= T^(2/7) Z, without rounding powers.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace TripleAdoptEighthMomentRatio

theorem bound (N T Z : ℝ) (hZ : 1 ≤ Z) (hNZ : Z ≤ N) (hT : 0 ≤ T)
    (hrange : T ^ 2 * Z ^ 7 ≤ N ^ 7) :
    (T / N ^ 6) ^ (1 / 5 : ℝ) * (1 + T / N ^ 3) ≤ 2 / Z := by
  have hZp : 0 < Z := by linarith
  have hNp : 0 < N := by linarith
  have hNone : 1 ≤ N := hZ.trans hNZ
  have hZ35 : Z ^ 3 ≤ N ^ 5 :=
    (pow_le_pow_left₀ hZp.le hNZ 3).trans (pow_le_pow_right₀ hNone (by norm_num : 3 ≤ 5))
  have hfirst : T * Z ^ 5 ≤ N ^ 6 := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ T * Z ^ 5) (by positivity : 0 ≤ N ^ 6)).mp
    calc
      _ = (T ^ 2 * Z ^ 7) * Z ^ 3 := by ring
      _ ≤ N ^ 7 * N ^ 5 := mul_le_mul hrange hZ35 (by positivity) (by positivity)
      _ = _ := by ring
  have hsecond : T ^ 6 * Z ^ 5 ≤ N ^ 21 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ T ^ 2 * Z ^ 7) hrange 3
    have hz : Z ^ 5 ≤ Z ^ 21 := pow_le_pow_right₀ hZ (by norm_num)
    calc
      _ ≤ T ^ 6 * Z ^ 21 := mul_le_mul_of_nonneg_left hz (by positivity)
      _ = (T ^ 2 * Z ^ 7) ^ 3 := by ring
      _ ≤ (N ^ 7) ^ 3 := hh
      _ = _ := by ring
  let R := (T / N ^ 6) ^ (1 / 5 : ℝ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hR5 : R ^ 5 = T / N ^ 6 := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ T / N ^ 6)]
    norm_num
  have hsmall : R ≤ 1 / Z := by
    apply (pow_le_pow_iff_left₀ hR (by positivity : 0 ≤ 1 / Z) (by norm_num : (5 : ℕ) ≠ 0)).mp
    rw [hR5, div_pow, one_pow]
    exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hfirst)
  have hlarge : R * (T / N ^ 3) ≤ 1 / Z := by
    apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ R * (T / N ^ 3))
      (by positivity : 0 ≤ 1 / Z) (by norm_num : (5 : ℕ) ≠ 0)).mp
    rw [mul_pow, hR5, div_pow, div_pow, one_pow]
    apply (le_div_iff₀ (by positivity : 0 < Z ^ 5)).mpr
    calc
      (T / N ^ 6 * (T ^ 5 / (N ^ 3) ^ 5)) * Z ^ 5 = (T ^ 6 * Z ^ 5) / N ^ 21 := by
        field_simp
      _ ≤ 1 := (div_le_one (by positivity)).mpr hsecond
  change R * (1 + T / N ^ 3) ≤ 2 / Z
  calc
    _ = R + R * (T / N ^ 3) := by ring
    _ ≤ 1 / Z + 1 / Z := add_le_add hsmall hlarge
    _ = _ := by ring

end TripleAdoptEighthMomentRatio

#print axioms TripleAdoptEighthMomentRatio.bound
run_cmd do
  let axioms ← Lean.collectAxioms ``TripleAdoptEighthMomentRatio.bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "EIGHTH MOMENT RATIO PASSED"
