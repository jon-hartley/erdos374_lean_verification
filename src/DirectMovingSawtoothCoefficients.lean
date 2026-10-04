import DirectMovingSawtooth

/-! Exact Fourier coefficients of the centered sawtooth. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set intervalIntegral
open scoped Real ENNReal BigOperators

namespace DirectMovingSawtooth
open PairFourier

theorem exp_primitive_hasDeriv (c : ℂ) (hc : c≠0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (c*t)/c) (Complex.exp (c*x)) x := by
  conv => congr
  rw [←mul_div_cancel_right₀ (Complex.exp (c*x)) hc]
  apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
  simpa only [mul_one] using! ((hasDerivAt_id (x:ℂ)).const_mul c).comp_ofReal

theorem phase_integral_zero (n : ℕ) (hn : 0<n) (k : ℤ) (hk : k≠0) :
    (∫x in (0:ℝ)..n, phase n k x) = 0 := by
  rw [integral_phase n (by exact_mod_cast hn.ne') k hk, phase_at_period,
    phase_at_zero, sub_self, mul_zero]

theorem integral_x_mul_phase (n : ℕ) (hn : 0<n) (k : ℤ) (hk : k≠0) :
    (∫x in (0:ℝ)..n, (x:ℂ)*phase n k x) =
      (n:ℂ)/((2*π*Complex.I*k:ℂ)/n) := by
  let c : ℂ := (2*π*Complex.I*k:ℂ)/n
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  have hkC : (k:ℂ)≠0 := by exact_mod_cast hk
  have hpC : (π:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : c≠0 := div_ne_zero (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hpC) Complex.I_ne_zero) hkC) hnC
  have he (x : ℝ) : phase n k x = Complex.exp (c*x) := by
    rw [phase, fourier_coe_apply]
    congr 1
    dsimp [c]
    ring
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => phase n k t/c) (phase n k x) x := by
    simpa only [he] using exp_primitive_hasDeriv c hc x
  have hi := integral_mul_deriv_eq_deriv_mul
    (u:=fun x : ℝ => (x:ℂ)) (u':=fun _ => (1:ℂ))
    (v:=fun x : ℝ => phase n k x/c) (v':=phase n k)
    (a:=0) (b:=(n:ℝ))
    (fun x _ => (hasDerivAt_id (x:ℂ)).comp_ofReal)
    (fun x _ => hd x) (continuous_const.intervalIntegrable _ _)
    ((phase_continuous n k).intervalIntegrable _ _)
  simp only [Complex.ofReal_zero, phase_at_period, phase_at_zero, zero_mul,
    sub_zero, one_mul] at hi
  rw [intervalIntegral.integral_div, phase_integral_zero n hn k hk, zero_div, sub_zero] at hi
  simpa only [mul_one_div, Complex.ofReal_natCast] using hi

theorem coefficient_ne_zero (n : ℕ) (hn : 0<n) (k : ℤ) (hk : k≠0) :
    fourierCoeffOn (show (0:ℝ)<n by exact_mod_cast hn) (sawtooth n) k =
      1/(2*π*Complex.I*k) := by
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  have hkC : (k:ℂ)≠0 := by exact_mod_cast hk
  have hpC : (π:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hint : (∫x in (0:ℝ)..n, phase n (-k) x*sawtooth n x) =
      (1/2:ℂ)*(∫x in (0:ℝ)..n, phase n (-k) x) -
        (1/(n:ℂ))*(∫x in (0:ℝ)..n, (x:ℂ)*phase n (-k) x) := by
    rw [integral_mul_eq_affine n hn]
    have he (x : ℝ) : phase n (-k) x*((1/2:ℂ)-(x:ℂ)/(n:ℂ)) =
        (1/2:ℂ)*phase n (-k) x - (1/(n:ℂ))*((x:ℂ)*phase n (-k) x) := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_sub
      (f:=fun x : ℝ => (1/2:ℂ)*phase n (-k) x)
      (g:=fun x : ℝ => (1/(n:ℂ))*((x:ℂ)*phase n (-k) x))
      ((continuous_const.mul (phase_continuous n (-k))).intervalIntegrable _ _)
      ((continuous_const.mul (Complex.continuous_ofReal.mul
        (phase_continuous n (-k)))).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [PairFourier.coefficient_eq_integral, hint,
    phase_integral_zero n hn (-k) (neg_ne_zero.mpr hk),
    integral_x_mul_phase n hn (-k) (neg_ne_zero.mpr hk)]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_natCast, Int.cast_neg]
  field_simp
  ring

theorem coefficient_norm_le (n : ℕ) (hn : 0<n) (k : ℤ) (hk : k≠0) :
    ‖fourierCoeffOn (show (0:ℝ)<n by exact_mod_cast hn) (sawtooth n) k‖ ≤
      1/(π*|(k:ℝ)|) := by
  rw [coefficient_ne_zero n hn k hk, norm_div, norm_one]
  have hd : ‖(2*π*Complex.I*k:ℂ)‖ = 2*π*|(k:ℝ)| := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_intCast, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
  rw [hd]
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk
  apply one_div_le_one_div_of_le (mul_pos Real.pi_pos (abs_pos.mpr hkR))
  nlinarith [mul_pos Real.pi_pos (abs_pos.mpr hkR)]

run_cmd do
  for decl in [``exp_primitive_hasDeriv, ``phase_integral_zero, ``integral_x_mul_phase,
      ``coefficient_ne_zero, ``coefficient_norm_le] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT POSITIVE SAWTOOTH FOURIER COEFFICIENTS PASSED"

end DirectMovingSawtooth
