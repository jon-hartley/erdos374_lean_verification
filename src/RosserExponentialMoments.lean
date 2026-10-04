import RosserKernelIntegral

/-! Exact exponential moments used in estimating arithmetic kernel errors.
These are ordinary improper integrals and elementary polynomial inequalities;
no estimate for primes or transfer from a discrete stopping sum is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology

namespace RosserExponentialMoments

def poly1 (a : ℝ) : ℝ := a+2
def poly2 (a : ℝ) : ℝ := a^2+4*a+5
def poly3 (a : ℝ) : ℝ := a^3+6*a^2+15*a+16

theorem monomial_limit (n : ℕ) :
    Tendsto (fun s : ℝ => s^n * exp (-s)) atTop (𝓝 0) := by
  simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n:ℝ) 1 (by norm_num)

theorem exp_limit : Tendsto (fun s : ℝ => exp (-s)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

theorem moment1_deriv (s : ℝ) :
    HasDerivAt (fun x : ℝ => -exp (-x)*poly1 x) (exp (-s)*(s+1)^1) s := by
  convert! (((hasDerivAt_id s).neg.exp).neg.mul ((hasDerivAt_id s).add_const 2)) using 1
  all_goals solve | rfl | (dsimp [poly1]; ring)

theorem moment2_deriv (s : ℝ) :
    HasDerivAt (fun x : ℝ => -exp (-x)*poly2 x) (exp (-s)*(s+1)^2) s := by
  convert! (((hasDerivAt_id s).neg.exp).neg.mul
    ((((hasDerivAt_id s).pow 2).add ((hasDerivAt_id s).const_mul 4)).add_const 5)) using 1
  all_goals solve | rfl | (dsimp [poly2]; ring)

theorem moment3_deriv (s : ℝ) :
    HasDerivAt (fun x : ℝ => -exp (-x)*poly3 x) (exp (-s)*(s+1)^3) s := by
  convert! (((hasDerivAt_id s).neg.exp).neg.mul
    (((((hasDerivAt_id s).pow 3).add (((hasDerivAt_id s).pow 2).const_mul 6)).add
      ((hasDerivAt_id s).const_mul 15)).add_const 16)) using 1
  all_goals solve | rfl | (dsimp [poly3]; ring)

theorem moment1_limit :
    Tendsto (fun s : ℝ => -exp (-s)*poly1 s) atTop (𝓝 0) := by
  have h := ((monomial_limit 1).add (exp_limit.const_mul 2)).neg
  simp only [mul_zero, add_zero, neg_zero] at h
  convert h using 1
  ext s
  dsimp [poly1]
  ring

theorem moment2_limit :
    Tendsto (fun s : ℝ => -exp (-s)*poly2 s) atTop (𝓝 0) := by
  have h := (((monomial_limit 2).add ((monomial_limit 1).const_mul 4)).add
    (exp_limit.const_mul 5)).neg
  simp only [mul_zero, add_zero, neg_zero] at h
  convert h using 1
  ext s
  dsimp [poly2]
  ring

theorem moment3_limit :
    Tendsto (fun s : ℝ => -exp (-s)*poly3 s) atTop (𝓝 0) := by
  have h := ((((monomial_limit 3).add ((monomial_limit 2).const_mul 6)).add
    ((monomial_limit 1).const_mul 15)).add (exp_limit.const_mul 16)).neg
  simp only [mul_zero, add_zero, neg_zero] at h
  convert h using 1
  ext s
  dsimp [poly3]
  ring

theorem moment_nonneg (a s : ℝ) (n : ℕ) (ha : 1 ≤ a) (hs : s ∈ Ioi a) :
    0 ≤ exp (-s)*(s+1)^n :=
  mul_nonneg (exp_pos _).le (pow_nonneg (by linarith [hs.out]) _)

theorem moment1_integrable (a : ℝ) (ha : 1 ≤ a) :
    IntegrableOn (fun s : ℝ => exp (-s)*(s+1)^1) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun s _ => moment1_deriv s)
    (fun s hs => moment_nonneg a s 1 ha hs) moment1_limit

theorem moment2_integrable (a : ℝ) (ha : 1 ≤ a) :
    IntegrableOn (fun s : ℝ => exp (-s)*(s+1)^2) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun s _ => moment2_deriv s)
    (fun s hs => moment_nonneg a s 2 ha hs) moment2_limit

theorem moment3_integrable (a : ℝ) (ha : 1 ≤ a) :
    IntegrableOn (fun s : ℝ => exp (-s)*(s+1)^3) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun s _ => moment3_deriv s)
    (fun s hs => moment_nonneg a s 3 ha hs) moment3_limit

theorem moment1_integral (a : ℝ) (ha : 1 ≤ a) :
    (∫ s in Ioi a, exp (-s)*(s+1)^1) = exp (-a)*(a+2) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (fun s _ => moment1_deriv s)
    (fun s hs => moment_nonneg a s 1 ha hs) moment1_limit
  simpa [poly1] using h

theorem moment2_integral (a : ℝ) (ha : 1 ≤ a) :
    (∫ s in Ioi a, exp (-s)*(s+1)^2) = exp (-a)*(a^2+4*a+5) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (fun s _ => moment2_deriv s)
    (fun s hs => moment_nonneg a s 2 ha hs) moment2_limit
  simpa [poly2] using h

theorem moment3_integral (a : ℝ) (ha : 1 ≤ a) :
    (∫ s in Ioi a, exp (-s)*(s+1)^3) = exp (-a)*(a^3+6*a^2+15*a+16) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (fun s _ => moment3_deriv s)
    (fun s hs => moment_nonneg a s 3 ha hs) moment3_limit
  simpa [poly3] using h

theorem normalized_poly1 (r : ℝ) (hr : 2 ≤ r) : (r+1)/r^2 ≤ 3/4 := by
  rw [div_le_iff₀ (pow_pos (by linarith : 0 < r) 2)]
  have h := mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ 3*r+2 by linarith)
  nlinarith

theorem normalized_poly2 (r : ℝ) (hr : 2 ≤ r) : (r^2+2*r+2)/r^3 ≤ 5/4 := by
  rw [div_le_iff₀ (pow_pos (by linarith : 0 < r) 3)]
  have h := mul_nonneg (sub_nonneg.mpr hr)
    (show 0 ≤ 5*r^2+6*r+4 by nlinarith [sq_nonneg r])
  nlinarith

theorem normalized_poly3 (r : ℝ) (hr : 2 ≤ r) :
    (r^3+3*r^2+6*r+6)/r^4 ≤ 19/8 := by
  rw [div_le_iff₀ (pow_pos (by linarith : 0 < r) 4)]
  have hr0 : 0 ≤ r := by linarith
  have h := mul_nonneg (sub_nonneg.mpr hr)
    (show 0 ≤ 19*r^3+30*r^2+36*r+24 by positivity)
  nlinarith

run_cmd do
  for decl in [``poly1, ``poly2, ``poly3, ``monomial_limit, ``exp_limit,
      ``moment1_deriv, ``moment2_deriv, ``moment3_deriv,
      ``moment1_limit, ``moment2_limit, ``moment3_limit, ``moment_nonneg,
      ``moment1_integrable, ``moment2_integrable, ``moment3_integrable,
      ``moment1_integral, ``moment2_integral, ``moment3_integral,
      ``normalized_poly1, ``normalized_poly2, ``normalized_poly3] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT EXPONENTIAL MOMENTS AND NORMALIZED POLYNOMIAL BOUNDS PASSED"

end RosserExponentialMoments
end
