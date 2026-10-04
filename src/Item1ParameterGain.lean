import Item1ParameterGainDiscrete

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Item1ParameterGain
open Item1ParameterCore

theorem gain_sub_eta_small (a : ℝ) (ha : 1 ≤ a) (hb : a ≤ 2) :
    (7/75:ℝ)*a^2 ≤ totalGain (degree a) a-etaLoss (degree a) := by
  have hs := totalGain_small a ha hb
  have hd := degree_ge_five a ha
  have he := etaLoss_le (degree a) (by omega)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (degree a)) (degree_le_six a ha) 2
  nlinarith

theorem gain_sub_eta_large (a : ℝ) (ha : 2 ≤ a) :
    (19/600:ℝ)*a^2 ≤ totalGain (degree a) a-etaLoss (degree a) := by
  have hs := totalGain_large a ha
  have hd := degree_ge_five a (by linarith)
  have he := etaLoss_le (degree a) (by omega)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (degree a)) (degree_le_nine_halves a ha) 2
  nlinarith

/-- The uniform discrete model margin, including all values a >= 1. -/
theorem gain_sub_eta (a : ℝ) (ha : 1 ≤ a) :
    a^2/40 ≤ totalGain (degree a) a-etaLoss (degree a) := by
  rcases le_total a 2 with h | h
  · have hs := gain_sub_eta_small a ha h
    nlinarith [sq_nonneg a]
  · have hs := gain_sub_eta_large a h
    nlinarith [sq_nonneg a]

theorem gain_parameter_bounds (a : ℝ) (ha : 1 ≤ a) :
    5 ≤ degree a ∧ (degree a:ℝ) ≤ 6*a ∧
      a^2/40 ≤ totalGain (degree a) a-etaLoss (degree a) :=
  ⟨degree_ge_five a ha, degree_le_six a ha, gain_sub_eta a ha⟩

end Item1ParameterGain

run_cmd do
  for target in [``Item1ParameterGain.gain_sub_eta_small,
      ``Item1ParameterGain.gain_sub_eta_large, ``Item1ParameterGain.gain_sub_eta,
      ``Item1ParameterGain.gain_parameter_bounds] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER GAIN: 4 standard-axiom theorem guards passed."
