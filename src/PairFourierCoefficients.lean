import PairFourierBasics

/-! Exact Fourier coefficients of the integer-floor discrepancy. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set intervalIntegral
open scoped Real ENNReal

namespace PairFourier

def phase (T : ℝ) (k : ℤ) (x : ℝ) : ℂ := fourier k (x : AddCircle T)

theorem phase_continuous (T : ℝ) (k : ℤ) : Continuous (phase T k) := by
  unfold phase
  simp only [fourier_coe_apply]
  fun_prop

theorem phase_periodic (T : ℝ) (k : ℤ) : Function.Periodic (phase T k) T := by
  intro x
  simp only [phase, AddCircle.coe_add_period]

theorem phase_zero (T : ℝ) (x : ℝ) : phase T 0 x = 1 := fourier_zero

theorem phase_at_zero (T : ℝ) (k : ℤ) : phase T k 0 = 1 := by
  simp [phase]

theorem phase_at_period (T : ℝ) (k : ℤ) : phase T k T = 1 := by
  rw [phase, AddCircle.coe_period, fourier_eval_zero]

theorem phase_norm (T : ℝ) (k : ℤ) (x : ℝ) : ‖phase T k x‖ = 1 := by
  exact Circle.norm_coe _

theorem integral_phase (T : ℝ) (hT : T ≠ 0) (k : ℤ) (hk : k ≠ 0) (a b : ℝ) :
    (∫ x in a..b, phase T k x) =
      (T : ℂ) / (2 * π * Complex.I * k) * (phase T k b - phase T k a) := by
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
  have hkc : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : (2 * π * Complex.I * k / T : ℂ) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi)
      Complex.I_ne_zero) hkc) hTc
  have he (x : ℝ) : phase T k x = Complex.exp ((2*π*Complex.I*k/T) * x) := by
    rw [phase, fourier_coe_apply]
    congr 1
    ring
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  field_simp

/-- Integrating against any continuous test function uses the literal floor
step, with both endpoints handled by interval-integral congruence. -/
theorem integral_mul_discrepancy {n : ℕ} (hn : 0 < n) (h : ℝ)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ x in (0 : ℝ)..n, f x * discrepancy n h x) =
      (∫ x in (0 : ℝ)..(n:ℝ)*Int.fract (h/n), f x) -
        ((Int.fract (h/(n:ℝ)) : ℝ) : ℂ) * (∫ x in (0 : ℝ)..n, f x) := by
  let u := Int.fract (h/(n:ℝ))
  let c := (n:ℝ)*u
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hc0 : 0 ≤ c := mul_nonneg hnR.le (Int.fract_nonneg _)
  have hcn : c ≤ n := by
    exact (mul_le_mul_of_nonneg_left (Int.fract_lt_one _).le hnR.le).trans_eq (mul_one _)
  have hi (a b : ℝ) : IntervalIntegrable (fun x => f x * discrepancy n h x) volume a b := by
    simpa only [mul_comm] using
      (discrepancy_intervalIntegrable n h a b).mul_continuousOn hf.continuousOn
  have hl : (∫ x in (0 : ℝ)..c, f x * discrepancy n h x) =
      (1-(u:ℂ)) * (∫ x in (0 : ℝ)..c, f x) := by
    calc
      _ = ∫ x in (0 : ℝ)..c, (1-(u:ℂ)) * f x := by
        apply integral_congr_Ioo_of_le hc0
        intro x hx
        dsimp only [discrepancy]
        rw [discrepancy_step hn h x hx.1.le (hx.2.trans_le hcn),
          ite_eq_left hx.2]
        push_cast
        ring
      _ = _ := integral_const_mul _ _
  have hr : (∫ x in c..(n:ℝ), f x * discrepancy n h x) =
      -(u:ℂ) * (∫ x in c..(n:ℝ), f x) := by
    calc
      _ = ∫ x in c..(n:ℝ), -(u:ℂ) * f x := by
        apply integral_congr_Ioo_of_le hcn
        intro x hx
        dsimp only [discrepancy]
        rw [discrepancy_step hn h x (hc0.trans hx.1.le) hx.2,
          ite_eq_right (not_lt.mpr hx.1.le)]
        push_cast
        ring
      _ = _ := integral_const_mul _ _
  rw [← integral_add_adjacent_intervals (hi 0 c) (hi c n), hl, hr,
    ← integral_add_adjacent_intervals (hf.intervalIntegrable 0 c) (hf.intervalIntegrable c n)]
  change (1-(u:ℂ)) * _ + -(u:ℂ) * _ = _
  ring

theorem phase_fract_mul {n : ℕ} (hn : 0 < n) (h : ℝ) (k : ℤ) :
    phase n k ((n:ℝ)*Int.fract (h/n)) = phase n k h := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (n:ℝ)*Int.fract (h/n) = h - (⌊h/n⌋:ℝ)*(n:ℝ) := by
    unfold Int.fract
    field_simp
  rw [he, phase, AddCircle.coe_sub, ← zsmul_eq_mul, AddCircle.coe_zsmul,
    AddCircle.coe_period, smul_zero, sub_zero]
  rfl

theorem coefficient_zero {n : ℕ} (hn : 0 < n) (h : ℝ) :
    fourierCoeffOn (show (0:ℝ)<n by exact_mod_cast hn) (discrepancy n h) 0 = 0 := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, neg_zero, fourier_zero, one_smul]
  have hm := integral_mul_discrepancy hn h (fun _ => (1:ℂ)) continuous_const
  simp only [one_mul, intervalIntegral.integral_const, Complex.real_smul,
    sub_zero, mul_one] at hm
  rw [hm]
  push_cast
  simp [mul_comm]

theorem coefficient_eq_integral (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (k : ℤ) :
    fourierCoeffOn hT f k = (1/T) • (∫ x in (0:ℝ)..T, phase T (-k) x * f x) := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, smul_eq_mul, phase, fourier_coe_apply]

theorem coefficient_ne_zero {n : ℕ} (hn : 0 < n) (h : ℝ) {k : ℤ} (hk : k ≠ 0) :
    fourierCoeffOn (show (0:ℝ)<n by exact_mod_cast hn) (discrepancy n h) k =
      (1 - phase n (-k) h) / (2 * π * Complex.I * k) := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hkc : (k:ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hpi : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [coefficient_eq_integral,
    integral_mul_discrepancy hn h _ (phase_continuous _ _),
    integral_phase n hnR (-k) (neg_ne_zero.mpr hk),
    integral_phase n hnR (-k) (neg_ne_zero.mpr hk),
    phase_at_period, phase_at_zero, sub_self, mul_zero, mul_zero, sub_zero,
    phase_fract_mul hn]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_natCast, Int.cast_neg]
  field_simp
  ring

theorem coefficient_exp {n : ℕ} (hn : 0 < n) (h : ℝ) {k : ℤ} (hk : k ≠ 0) :
    fourierCoeffOn (show (0:ℝ)<n by exact_mod_cast hn) (discrepancy n h) k =
      (1 - Complex.exp (-2 * π * Complex.I * k * h / n)) /
        (2 * π * Complex.I * k) := by
  rw [coefficient_ne_zero hn h hk, phase, fourier_coe_apply]
  congr 3
  push_cast
  ring

theorem coefficient_norm_le {n : ℕ} (hn : 0 < n) (h : ℝ) {k : ℤ} (hk : k ≠ 0) :
    ‖fourierCoeffOn (show (0:ℝ)<n by exact_mod_cast hn) (discrepancy n h) k‖ ≤
      1 / (π * |(k:ℝ)|) := by
  rw [coefficient_ne_zero hn h hk, norm_div]
  have hb : ‖1 - phase n (-k) h‖ ≤ (2:ℝ) := by
    have hb' := norm_sub_le (1:ℂ) (phase n (-k) h)
    norm_num only [norm_one, phase_norm] at hb'
    exact hb'
  have hd : ‖(2 * π * Complex.I * k : ℂ)‖ = 2 * π * |(k:ℝ)| := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_intCast, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
  rw [hd]
  calc
    _ ≤ 2 / (2 * π * |(k:ℝ)|) := div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by ring

end PairFourier
