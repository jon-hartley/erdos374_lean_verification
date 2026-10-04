import Item1DyadicPhaseReduction

/-! Absorption of arbitrary fixed constants in the intermediate phase range.
This scalar estimate supplies no exponential-sum cancellation. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Item1PhaseConstantAbsorption

theorem coefficient_le_half (c y : ℝ) (hc : 0 < c) (hy : 1 ≤ y)
    (hcy : 1 ≤ c*y) : 1/(200*y^2) ≤ c/2 := by
  have hy0 : 0 < y := by linarith only [hy]
  have hy2 : y ≤ y^2 := by nlinarith only [hy]
  have hcy2 : 1 ≤ c*y^2 :=
    hcy.trans (mul_le_mul_of_nonneg_left hy2 hc.le)
  apply (div_le_iff₀ (by positivity : 0 < 200*y^2)).mpr
  nlinarith only [hcy2]

/-- The conditions are uniform in q. In the phase application, y=log log t
and q=(log M)^3/(log t)^2. -/
theorem fixed_constant_absorption (C c q y : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hy : 1 ≤ y)
    (hcy : 1 ≤ c*y) (hCy : C ≤ c*y) (hq : 2*y ≤ q) :
    C*Real.exp (-c*q) ≤ 16*Real.exp (-(q/(200*y^2))) := by
  have hq0 : 0 ≤ q := by linarith only [hy,hq]
  have ha := coefficient_le_half c y hc hy hcy
  have hCq : C ≤ (c/2)*q := by
    have hh := mul_le_mul_of_nonneg_left hq (show 0 ≤ c/2 by positivity)
    nlinarith only [hCy,hh]
  have hlog : Real.log C ≤ C := by
    have hh := Real.log_le_sub_one_of_pos hC
    linarith only [hh]
  have hsave : q/(200*y^2) ≤ (c/2)*q := by
    have hh := mul_le_mul_of_nonneg_right ha hq0
    simpa only [div_mul_eq_mul_div,one_mul] using hh
  have he : Real.log C-c*q ≤ -(q/(200*y^2)) := by
    nlinarith only [hlog,hCq,hsave]
  calc
    C*Real.exp (-c*q) = Real.exp (Real.log C-c*q) := by
      rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hC]
      congr 1
      ring
    _ ≤ Real.exp (-(q/(200*y^2))) := Real.exp_le_exp.mpr he
    _ ≤ 16*Real.exp (-(q/(200*y^2))) := by
      nlinarith only [Real.exp_pos (-(q/(200*y^2)))]

end Item1PhaseConstantAbsorption

run_cmd do
  for target in [``Item1PhaseConstantAbsorption.coefficient_le_half,
      ``Item1PhaseConstantAbsorption.fixed_constant_absorption] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1PhaseConstantAbsorption: 2 theorem guards passed."
