import Item1ParameterCore

/-! Exact Taylor coefficients and explicit bounds on their reciprocals. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Item1ParameterArithmeticCoefficient
open Item1LogPhasePolynomialReduction

theorem third_power (M : ℝ) (j : ℕ) (hM : 0 ≤ M) :
    (M^(1/3:ℝ))^j = M^((j:ℝ)/3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
  congr 1
  ring

theorem phaseCoefficient_abs (x t : ℝ) (j : ℕ)
    (hx : 0 < x) (ht : 0 ≤ t) (hj : 1 ≤ j) :
    |phaseCoefficient x t (j-1)/(2*Real.pi)| =
      t/(2*Real.pi*(j:ℝ)*x^j) := by
  have hj1 : j-1+1=j := Nat.sub_add_cancel hj
  have hjR : ((j-1:ℕ):ℝ)+1=(j:ℝ) := by exact_mod_cast hj1
  have hden : 0 < (((j-1:ℕ):ℝ)+1)*x^(j-1+1) := by positivity
  have hpi : 0 < 2*Real.pi := by positivity
  rw [abs_div, abs_of_pos hpi]
  unfold phaseCoefficient
  rw [abs_div, abs_of_pos hden, abs_mul]
  simp only [abs_neg, abs_pow, abs_one, one_pow, abs_of_nonneg ht, mul_one]
  rw [hj1, hjR]
  ring

theorem phaseCoefficient_bounds (M lam x : ℝ) (j : ℕ)
    (hM : 1 ≤ M) (hx : M ≤ x) (hx2 : x ≤ 2*M) (hj : 1 ≤ j) :
    phaseCoefficient x (M^lam) (j-1)/(2*Real.pi) ≠ 0 ∧
    |phaseCoefficient x (M^lam) (j-1)/(2*Real.pi)| ≤ M^(lam-(j:ℝ)) ∧
    1/|phaseCoefficient x (M^lam) (j-1)/(2*Real.pi)| ≤
      8*(j:ℝ)*(2:ℝ)^j*M^((j:ℝ)-lam) := by
  have hM0 : 0 < M := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le hM0 hx
  have hjR : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hj0 : (0:ℝ) < (j:ℝ) := by linarith
  have ht : 0 < M^lam := Real.rpow_pos_of_pos hM0 lam
  have hpi : 0 < 2*Real.pi := by positivity
  have hden : 0 < 2*Real.pi*(j:ℝ)*x^j := by positivity
  have habs := phaseCoefficient_abs x (M^lam) j hx0 ht.le hj
  have hgpos : 0 < |phaseCoefficient x (M^lam) (j-1)/(2*Real.pi)| := by
    rw [habs]
    exact div_pos ht hden
  refine ⟨abs_pos.mp hgpos, ?_, ?_⟩
  · rw [habs]
    have hpi1 : 1 ≤ 2*Real.pi*(j:ℝ) := by
      have hpi3 := Real.pi_gt_three
      nlinarith
    have hdenlower : M^j ≤ 2*Real.pi*(j:ℝ)*x^j := by
      calc
        M^j ≤ x^j := pow_le_pow_left₀ hM0.le hx j
        _ ≤ 2*Real.pi*(j:ℝ)*x^j := le_mul_of_one_le_left (by positivity) hpi1
    calc
      M^lam/(2*Real.pi*(j:ℝ)*x^j) ≤ M^lam/M^j :=
        div_le_div_of_nonneg_left ht.le (by positivity) hdenlower
      _ = M^(lam-(j:ℝ)) := by rw [Real.rpow_sub hM0, Real.rpow_natCast]
  · rw [habs, one_div_div]
    have hpi8 : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
    have hdenupper : 2*Real.pi*(j:ℝ)*x^j ≤ 8*(j:ℝ)*(2:ℝ)^j*M^j := by
      calc
        2*Real.pi*(j:ℝ)*x^j ≤ 8*(j:ℝ)*(2*M)^j := by gcongr
        _ = 8*(j:ℝ)*(2:ℝ)^j*M^j := by rw [mul_pow]; ring
    calc
      (2*Real.pi*(j:ℝ)*x^j)/M^lam ≤ (8*(j:ℝ)*(2:ℝ)^j*M^j)/M^lam :=
        div_le_div_of_nonneg_right hdenupper ht.le
      _ = 8*(j:ℝ)*(2:ℝ)^j*M^((j:ℝ)-lam) := by
        rw [Real.rpow_sub hM0, Real.rpow_natCast]
        ring

end Item1ParameterArithmeticCoefficient

run_cmd do
  for target in [``Item1ParameterArithmeticCoefficient.third_power,
      ``Item1ParameterArithmeticCoefficient.phaseCoefficient_abs,
      ``Item1ParameterArithmeticCoefficient.phaseCoefficient_bounds] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER ARITHMETIC COEFFICIENT: 3 standard-axiom theorem guards passed."
