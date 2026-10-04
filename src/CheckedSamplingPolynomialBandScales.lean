import CheckedSamplingVaughanBands

/-!
Elementary scale comparisons for applying VaughanBands uniformly when both
band lengths are at least a fourth root of the original interval scale.
Fourth powers avoid introducing rounding conventions for fractional powers.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace PolynomialBandScales

theorem band_log_bounds (P D K : ℕ) (hP : 2 ≤ P) (hD : 0 < D) (hK : 0 < K)
    (hPD : P ≤ D ^ 4) (hDK : D * K ≤ 2 * P) :
    Real.log (P : ℝ) ≤ 4 * Real.log (D : ℝ) ∧
      Real.log (D : ℝ) ≤ 2 * Real.log (P : ℝ) ∧
      Real.log (2 * (K : ℝ)) ≤ 3 * Real.log (P : ℝ) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hDr : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hPtwo : (2 : ℝ) ≤ P := Nat.cast_le.mpr hP
  have hDup : D ≤ 2 * P := by nlinarith [Nat.mul_le_mul_left D (show 1 ≤ K by omega)]
  have hKup : K ≤ 2 * P := by nlinarith [Nat.mul_le_mul_right K (show 1 ≤ D by omega)]
  have hDupR : (D : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hDup
  have hKupR : (K : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hKup
  have hPsq : (4 : ℝ) ≤ (P : ℝ) ^ 2 := by nlinarith
  have hPcube : 4 * (P : ℝ) ≤ (P : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hPsq hPr.le]
  refine ⟨?_, ?_, ?_⟩
  · have hh := Real.log_le_log hPr (by exact_mod_cast hPD : (P : ℝ) ≤ (D : ℝ) ^ 4)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  · have hh := Real.log_le_log hDr (show (D : ℝ) ≤ (P : ℝ) ^ 2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  · have hh := Real.log_le_log (by positivity : 0 < 2 * (K : ℝ))
      (show 2 * (K : ℝ) ≤ (P : ℝ) ^ 3 by linarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh

theorem cutoff_from_fourth_power (cutoff P D : ℕ)
    (hc : cutoff ^ 4 ≤ P) (hPD : P ≤ D ^ 4) : cutoff ≤ D := by
  exact (Nat.pow_le_pow_iff_left (by norm_num : 4 ≠ 0)).mp (hc.trans hPD)

theorem near_scale_available (S P D K : ℕ)
    (hlogD : 0 ≤ Real.log (D : ℝ))
    (hlog : Real.log (D : ℝ) ≤ 2 * Real.log (P : ℝ))
    (hgrowth : (2 : ℝ) ^ (8 * S) * Real.log (P : ℝ) ^ (8 * S) ≤ (P : ℝ))
    (hPK : P ≤ K ^ 4) :
    Real.log (D : ℝ) ^ (2 * S) ≤ (K : ℝ) := by
  apply (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg K)
    (by norm_num : 4 ≠ 0)).mp
  calc
    _ = Real.log (D : ℝ) ^ (8 * S) := by rw [← pow_mul]; congr 1; omega
    _ ≤ (2 * Real.log (P : ℝ)) ^ (8 * S) := pow_le_pow_left₀ hlogD hlog _
    _ = (2 : ℝ) ^ (8 * S) * Real.log (P : ℝ) ^ (8 * S) := mul_pow _ _ _
    _ ≤ (P : ℝ) := hgrowth
    _ ≤ _ := by exact_mod_cast hPK

theorem polynomial_coefficient_upper (J P D K : ℕ) (w : ℝ)
    (hD : 2 ≤ D) (hK : 1 ≤ K) (hPD : P ≤ D ^ 4)
    (hw : |w| ≤ (P : ℝ) ^ (J + 1)) :
    2 * |w| ≤ (K : ℝ) * (D : ℝ) ^ (4 * (J + 1) + 1) ∧
      4 * |w| ≤ (K : ℝ) ^ 2 * (D : ℝ) ^ (4 * (J + 1) + 2) := by
  have hDr : (2 : ℝ) ≤ D := Nat.cast_le.mpr hD
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hpow : (P : ℝ) ^ (J + 1) ≤ (D : ℝ) ^ (4 * (J + 1)) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg P) (by exact_mod_cast hPD) _
  have hbase := hw.trans hpow
  have hDsq : (4 : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
  have hKsq : (1 : ℝ) ≤ (K : ℝ) ^ 2 := one_le_pow₀ hKr
  constructor
  · calc
      _ ≤ 2 * (D : ℝ) ^ (4 * (J + 1)) := mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ ≤ (D : ℝ) * (D : ℝ) ^ (4 * (J + 1)) :=
        mul_le_mul_of_nonneg_right hDr (by positivity)
      _ = (D : ℝ) ^ (4 * (J + 1) + 1) := by rw [pow_succ]; ring
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hKr
  · calc
      _ ≤ 4 * (D : ℝ) ^ (4 * (J + 1)) := mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ ≤ (D : ℝ) ^ 2 * (D : ℝ) ^ (4 * (J + 1)) :=
        mul_le_mul_of_nonneg_right hDsq (by positivity)
      _ = (D : ℝ) ^ (4 * (J + 1) + 2) := by rw [pow_add]; ring
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hKsq

theorem band_saving (A : ℕ) (P D K : ℝ)
    (hP : 0 ≤ P)
    (hlogP : 0 < Real.log P) (hlogD : 0 < Real.log D)
    (hW : 0 ≤ Real.log (2 * K)) (hDK : D * K ≤ 2 * P)
    (hlower : Real.log P ≤ 4 * Real.log D)
    (hupper : Real.log (2 * K) ≤ 3 * Real.log P)
    (hlarge : 24 * (4 : ℝ) ^ (A + 2) ≤ Real.log P) :
    4 * D * K * Real.log (2 * K) / Real.log D ^ (A + 2) ≤
      P / Real.log P ^ A := by
  have hnum : 4 * D * K * Real.log (2 * K) ≤ 24 * P * Real.log P := by
    have hh := mul_le_mul hDK hupper hW (by positivity : 0 ≤ 2 * P)
    nlinarith only [hh]
  have hden : Real.log P ^ (A + 2) ≤ (4 : ℝ) ^ (A + 2) * Real.log D ^ (A + 2) := by
    simpa only [mul_pow] using pow_le_pow_left₀ hlogP.le hlower (A + 2)
  have hinv : 1 / Real.log D ^ (A + 2) ≤ (4 : ℝ) ^ (A + 2) / Real.log P ^ (A + 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simpa only [one_mul] using hden
  calc
    _ ≤ (24 * P * Real.log P) * (1 / Real.log D ^ (A + 2)) := by
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_right hnum
        (show 0 ≤ (Real.log D ^ (A + 2))⁻¹ by positivity)
    _ ≤ (24 * P * Real.log P) * ((4 : ℝ) ^ (A + 2) / Real.log P ^ (A + 2)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (24 * (4 : ℝ) ^ (A + 2) / Real.log P) * (P / Real.log P ^ A) := by
      rw [pow_add (Real.log P) A 2]
      field_simp
    _ ≤ 1 * (P / Real.log P ^ A) :=
      mul_le_mul_of_nonneg_right ((div_le_one hlogP).mpr hlarge) (by positivity)
    _ = _ := one_mul _

end PolynomialBandScales

#print axioms PolynomialBandScales.band_saving
run_cmd do
  for target in [``PolynomialBandScales.band_log_bounds,
      ``PolynomialBandScales.cutoff_from_fourth_power,
      ``PolynomialBandScales.near_scale_available,
      ``PolynomialBandScales.polynomial_coefficient_upper,
      ``PolynomialBandScales.band_saving] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "POLYNOMIAL BAND SCALES PASSED"

run_cmd do
  for target in [``PolynomialBandScales.band_log_bounds,
      ``PolynomialBandScales.cutoff_from_fourth_power,
      ``PolynomialBandScales.near_scale_available,
      ``PolynomialBandScales.polynomial_coefficient_upper,
      ``PolynomialBandScales.band_saving] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
