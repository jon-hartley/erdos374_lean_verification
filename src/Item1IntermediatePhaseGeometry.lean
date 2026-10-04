import Item1DyadicPhaseReduction

/-! Scalar consequences of the original intermediate-range lower cutoff.
These inequalities do not assert an exponential-sum estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Item1IntermediatePhaseGeometry

/-- Cubing the original logarithmic lower cutoff gives a uniform lower
bound for the cubic saving parameter. -/
theorem intermediate_cubic_lower (L u : ℝ) (hL : 1 < L)
    (hu : 6 * L ^ (2 / 3 : ℝ) * Real.log L < u) :
    216 * (Real.log L) ^ 3 < u ^ 3 / L ^ 2 := by
  have hLp : 0 < L := lt_trans (by norm_num) hL
  have hlog : 0 < Real.log L := Real.log_pos hL
  have hpow : (L ^ (2 / 3 : ℝ)) ^ 3 = L ^ 2 := by
    rw [← Real.rpow_mul_natCast hLp.le (2 / 3 : ℝ) 3]
    norm_num
  have hbase : 0 ≤ 6 * L ^ (2 / 3 : ℝ) * Real.log L := by positivity
  have hc := pow_lt_pow_left₀ hu hbase (by norm_num : (3 : ℕ) ≠ 0)
  simp only [mul_pow, hpow] at hc
  apply (lt_div_iff₀ (sq_pos_of_pos hLp)).mpr
  convert hc using 1 <;> ring

/-- In the same range the cubic saving parameter is nonnegative. -/
theorem intermediate_cubic_nonneg (L u : ℝ) (hL : 1 < L)
    (hu : 6 * L ^ (2 / 3 : ℝ) * Real.log L < u) :
    0 ≤ u ^ 3 / L ^ 2 := by
  have hlog : 0 ≤ Real.log L := (Real.log_pos hL).le
  exact (show 0 ≤ 216 * (Real.log L) ^ 3 by positivity).trans
    (intermediate_cubic_lower L u hL hu).le

end Item1IntermediatePhaseGeometry

run_cmd do
  for target in [``Item1IntermediatePhaseGeometry.intermediate_cubic_lower,
      ``Item1IntermediatePhaseGeometry.intermediate_cubic_nonneg] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "INTERMEDIATE PHASE GEOMETRY: 2 standard-axiom theorem guards passed."
