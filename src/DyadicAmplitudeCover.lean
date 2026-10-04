import DyadicMoment

/-!
Construct a finite dyadic amplitude cover and bound its number of bands
by an explicit logarithm. This discharges the free covering parameter
in the moment decomposition.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace DyadicAmplitudeCover

theorem exists_cover (v U : ℝ) (hv : 0 < v) :
    ∃ J : ℕ, U ≤ (2 : ℝ) ^ J * v ∧
      (2 : ℝ) ^ J * v ≤ 2 * max U v ∧
      (J : ℝ) ≤ 1 + Real.log (max (U / v) 1) / Real.log 2 := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hsmall : U ≤ v
  · refine ⟨0, ?_, ?_, ?_⟩
    · simpa using hsmall
    · simp only [pow_zero, one_mul, max_eq_right hsmall]
      linarith
    · have hratio : U / v ≤ 1 := (div_le_one hv).mpr hsmall
      simp only [Nat.cast_zero, max_eq_right hratio, Real.log_one, zero_div, add_zero]
      norm_num
  · have hratio : 1 ≤ U / v := (one_le_div hv).mpr (le_of_not_ge hsmall)
    obtain ⟨n, hn, hnUpper⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
    refine ⟨n + 1, ?_, ?_, ?_⟩
    · exact ((div_lt_iff₀ hv).mp hnUpper).le
    · have hlower := (le_div_iff₀ hv).mp hn
      rw [max_eq_left (le_of_not_ge hsmall), pow_succ]
      nlinarith
    · have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ n) hn
      rw [Real.log_pow] at hlog
      have hquot : (n : ℝ) ≤ Real.log (U / v) / Real.log 2 :=
        (le_div_iff₀ hlogtwo).mpr hlog
      rw [max_eq_left hratio]
      push_cast
      linarith

end DyadicAmplitudeCover

#print axioms DyadicAmplitudeCover.exists_cover
run_cmd do
  let axioms ← Lean.collectAxioms ``DyadicAmplitudeCover.exists_cover
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "DYADIC AMPLITUDE COVER PASSED"
