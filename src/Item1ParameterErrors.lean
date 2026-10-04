import Item1ParameterCore

/-! Scalar control of the two explicit prefix errors at the proposed degree. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Item1ParameterErrors

theorem taylor_error_le_two (K t u m lam : ℝ) (d : ℕ)
    (hK0 : 0 ≤ K) (hK : K ≤ Real.exp m) (ht : t = Real.exp (lam*m))
    (hu0 : 0 ≤ u) (hu : u ≤ Real.exp (-m/3)) (hm : 0 ≤ m)
    (hd : 3*lam+2 ≤ (d:ℝ)) : K*(2*|t| *u^(d+1)) ≤ 2 := by
  rw [ht, abs_of_pos (Real.exp_pos _)]
  have hp : u^(d+1) ≤ Real.exp (((d:ℝ)+1)*(-m/3)) := by
    calc
      u^(d+1) ≤ (Real.exp (-m/3))^(d+1) := pow_le_pow_left₀ hu0 hu _
      _ = Real.exp (((d:ℝ)+1)*(-m/3)) := by
        rw [← Real.exp_nat_mul]
        norm_cast
  have he : (1+lam-((d:ℝ)+1)/3)*m ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hm
  calc
    K*(2*Real.exp (lam*m)*u^(d+1)) ≤
        Real.exp m*(2*Real.exp (lam*m)*Real.exp (((d:ℝ)+1)*(-m/3))) := by
          gcongr
    _ = 2*Real.exp ((1+lam-((d:ℝ)+1)/3)*m) := by
      rw [show (1+lam-((d:ℝ)+1)/3)*m =
        m+lam*m+((d:ℝ)+1)*(-m/3) by ring,
        Real.exp_add, Real.exp_add]
      ring
    _ ≤ 2 := by
      have h := Real.exp_le_one_iff.mpr he
      linarith

theorem boundary_scale_le (m lam : ℝ) (hm : 0 ≤ m) (hlam : 1 ≤ lam) :
    Real.exp (2*m/3) ≤ Real.exp m*Real.exp (-m/(4000000*lam^2)) := by
  have hden : (3:ℝ) ≤ 4000000*lam^2 := by nlinarith [sq_nonneg (lam-1)]
  have hdiv : m/(4000000*lam^2) ≤ m/3 :=
    div_le_div_of_nonneg_left hm (by norm_num) hden
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  linarith

theorem one_le_saving_scale (m lam : ℝ) (hm : 0 ≤ m) (hlam : 1 ≤ lam) :
    1 ≤ Real.exp m*Real.exp (-m/(4000000*lam^2)) := by
  exact (Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 2*m/3)).trans
    (boundary_scale_le m lam hm hlam)

theorem prefix_errors_absorbed (X m lam : ℝ) (hm : 0 ≤ m) (hlam : 1 ≤ lam)
    (hX : X ≤ Real.exp m*Real.exp (-m/(4000000*lam^2)) + 2 + 2*Real.exp (2*m/3)) :
    X ≤ 5*Real.exp m*Real.exp (-m/(4000000*lam^2)) := by
  have h1 := one_le_saving_scale m lam hm hlam
  have hb := boundary_scale_le m lam hm hlam
  nlinarith

end Item1ParameterErrors

run_cmd do
  for target in [``Item1ParameterErrors.taylor_error_le_two,
      ``Item1ParameterErrors.boundary_scale_le,
      ``Item1ParameterErrors.one_le_saving_scale,
      ``Item1ParameterErrors.prefix_errors_absorbed] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER ERRORS: 4 standard-axiom theorem guards passed."
