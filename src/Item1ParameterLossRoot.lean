import Item1ParameterCore

/-! Scalar extraction of a pointwise exponential saving from the chosen
positive even moment order. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Item1ParameterLossRoot
open Item1ParameterCore

theorem momentOrder_bound (d : ℕ) (lam : ℝ) (hlam : 1 ≤ lam)
    (hdlam : (d:ℝ) ≤ 6*lam) :
    ((2*momentOrder d*momentOrder d:ℕ):ℝ) ≤ 41472*lam^4 := by
  have hlam0 : 0 ≤ lam := by linarith
  simp only [momentOrder, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  calc
    2*(4*(d:ℝ)^2)*(4*(d:ℝ)^2) = 32*(d:ℝ)^4 := by ring
    _ ≤ 32*(6*lam)^4 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg d) hdlam 4) (by norm_num)
    _ = 41472*lam^4 := by ring

/-- A positive natural moment bounded by 41472*lambda^4 suffices for the
fixed exponential constant 1/4000000. -/
theorem exp_bound_of_pow_bound (p : ℕ) (m lam z : ℝ)
    (hp : 0 < p) (hm : 0 ≤ m) (hlam : 1 ≤ lam) (_hz : 0 ≤ z)
    (hpbound : (p:ℝ) ≤ 41472*lam^4)
    (hzpow : z^p ≤ Real.exp (-lam^2*m/80)) :
    z ≤ Real.exp (-m/(4000000*lam^2)) := by
  have hlampos : 0 < lam := by linarith
  have hcross : (p:ℝ)*80 ≤ 4000000*lam^4 := by
    nlinarith only [hpbound, pow_nonneg hlampos.le 4]
  have hfrac : (p:ℝ)/(4000000*lam^2) ≤ lam^2/80 := by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 4000000*lam^2)
      (by norm_num : (0:ℝ) < 80)).mpr
    convert hcross using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hfrac hm
  have harg : -lam^2*m/80 ≤ (p:ℝ)*(-m/(4000000*lam^2)) := by
    convert neg_le_neg hmul using 1 <;> ring
  apply le_of_pow_le_pow_left₀ hp.ne' (Real.exp_pos _).le
  calc
    z^p ≤ Real.exp (-lam^2*m/80) := hzpow
    _ ≤ Real.exp ((p:ℝ)*(-m/(4000000*lam^2))) := Real.exp_le_exp.mpr harg
    _ = (Real.exp (-m/(4000000*lam^2)))^p := Real.exp_nat_mul _ p

/-- The actual chosen even moment has the required positive order. -/
theorem moment_root_bound (d : ℕ) (m lam z : ℝ)
    (hd : 5 ≤ d) (hm : 0 ≤ m) (hlam : 1 ≤ lam) (hz : 0 ≤ z)
    (hdlam : (d:ℝ) ≤ 6*lam)
    (hzpow : z^(2*momentOrder d*momentOrder d) ≤ Real.exp (-lam^2*m/80)) :
    z ≤ Real.exp (-m/(4000000*lam^2)) := by
  have hdpos : 0 < d := by omega
  have hp : 0 < 2*momentOrder d*momentOrder d := by
    unfold momentOrder
    positivity
  exact exp_bound_of_pow_bound _ m lam z hp hm hlam hz
    (momentOrder_bound d lam hlam hdlam) hzpow

end Item1ParameterLossRoot

run_cmd do
  for target in [``Item1ParameterLossRoot.momentOrder_bound,
      ``Item1ParameterLossRoot.exp_bound_of_pow_bound,
      ``Item1ParameterLossRoot.moment_root_bound] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER LOSS ROOT: 3 standard-axiom theorem guards passed."
