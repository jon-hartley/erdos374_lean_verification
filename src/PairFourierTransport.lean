import PairFourierCoefficients

/-! Transport Fourier coefficients from a short period to an integer
multiple of that period, including exact vanishing of incompatible modes. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set intervalIntegral
open scoped Real

namespace PairFourierTransport
open PairFourier

theorem phase_add (T : ℝ) (k : ℤ) (x y : ℝ) :
    phase T k (x+y) = phase T k x * phase T k y := by
  simp only [phase, fourier_coe_apply, Complex.ofReal_add]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem phase_mul_period (T : ℝ) (M : ℕ) (hM : 0 < M) (k : ℤ) (x : ℝ) :
    phase ((M:ℝ)*T) ((M:ℤ)*k) x = phase T k x := by
  have hMC : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [phase, fourier_coe_apply, Complex.ofReal_mul, Complex.ofReal_natCast,
    Int.cast_mul, Int.cast_natCast]
  congr 1
  field_simp

theorem exp_int_div_eq_one_iff (k M : ℤ) (hM : M ≠ 0) :
    Complex.exp (2*π*Complex.I*k/M) = 1 ↔ M ∣ k := by
  rw [Complex.exp_eq_one_iff]
  have hMC : (M:ℂ) ≠ 0 := Int.cast_ne_zero.mpr hM
  have hc : (2*π*Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  constructor
  · rintro ⟨j, hj⟩
    have he : (k:ℂ) = (M:ℂ)*j := by
      apply (mul_left_cancel₀ hc)
      have hh := (div_eq_iff hMC).mp hj
      calc
        _ = (j:ℂ)*(2*π*Complex.I)*M := hh
        _ = _ := by ring
    have heZ : k=M*j := by exact_mod_cast he
    exact ⟨j, heZ⟩
  · rintro ⟨j, rfl⟩
    refine ⟨j, ?_⟩
    push_cast
    field_simp

theorem phase_at_small_period_ne_one (T : ℝ) (hT : 0 < T)
    (M : ℕ) (hM : 0 < M) (k : ℤ) (hk : ¬ (M:ℤ) ∣ k) :
    phase ((M:ℝ)*T) k T ≠ 1 := by
  have hTC : (T:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hMC : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have he : phase ((M:ℝ)*T) k T = Complex.exp (2*π*Complex.I*k/M) := by
    simp only [phase, fourier_coe_apply, Complex.ofReal_mul, Complex.ofReal_natCast]
    congr 1
    field_simp
  rw [he]
  exact fun h => hk ((exp_int_div_eq_one_iff k M (by exact_mod_cast hM.ne')).mp h)

theorem coefficient_mul_period (T : ℝ) (hT : 0 < T) (M : ℕ) (hM : 0 < M)
    (f : ℝ → ℂ) (hp : Function.Periodic f T)
    (hi : ∀ a b, IntervalIntegrable f volume a b) (k : ℤ) :
    fourierCoeffOn (mul_pos (show (0:ℝ)<M by exact_mod_cast hM) hT) f ((M:ℤ)*k) =
      fourierCoeffOn hT f k := by
  have hg : Function.Periodic (fun x => phase T (-k) x * f x) T :=
    (phase_periodic T (-k)).mul hp
  have hgi (a b : ℝ) : IntervalIntegrable (fun x => phase T (-k) x * f x) volume a b := by
    simpa only [mul_comm] using (hi a b).mul_continuousOn (phase_continuous T (-k)).continuousOn
  have hrepeat := hg.intervalIntegral_add_zsmul_eq (M:ℤ) 0 hgi
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast] at hrepeat
  rw [coefficient_eq_integral, coefficient_eq_integral]
  have hneg : -((M:ℤ)*k) = (M:ℤ)*(-k) := by ring
  simp_rw [hneg, phase_mul_period T M hM]
  rw [hrepeat]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_natCast]
  have hMC : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

theorem coefficient_eq_zero_of_not_dvd (T : ℝ) (hT : 0 < T) (M : ℕ) (hM : 0 < M)
    (f : ℝ → ℂ) (hp : Function.Periodic f T) (k : ℤ) (hk : ¬ (M:ℤ) ∣ k) :
    fourierCoeffOn (mul_pos (show (0:ℝ)<M by exact_mod_cast hM) hT) f k = 0 := by
  let P := (M:ℝ)*T
  let g := fun x => phase P (-k) x * f x
  have hfP : Function.Periodic f P := by
    simpa only [nsmul_eq_mul] using hp.nsmul M
  have hgP : Function.Periodic g P := (phase_periodic P (-k)).mul hfP
  have hphase : phase P (-k) T ≠ 1 :=
    phase_at_small_period_ne_one T hT M hM (-k) (by simpa only [dvd_neg] using hk)
  have hshift (x : ℝ) : g (x+T) = phase P (-k) T * g x := by
    dsimp only [g]
    rw [phase_add, hp x]
    ring
  have hI : (∫ x in 0..P, g x) = phase P (-k) T * (∫ x in 0..P, g x) := by
    calc
      _ = ∫ x in T..T+P, g x := by
        simpa only [zero_add] using hgP.intervalIntegral_add_eq 0 T
      _ = ∫ x in 0..P, g (x+T) := by
        rw [integral_comp_add_right]
        simp only [add_comm, add_zero]
      _ = _ := by simp_rw [hshift]; rw [intervalIntegral.integral_const_mul]
  have hz : (∫ x in 0..P, g x) = 0 := by
    have he : (phase P (-k) T - 1) * (∫ x in 0..P, g x) = 0 := by
      calc
        _ = phase P (-k) T * (∫ x in 0..P, g x) - (∫ x in 0..P, g x) := by ring
        _ = 0 := by rw [← hI, sub_self]
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hphase)
  rw [coefficient_eq_integral]
  change (1/P) • (∫ x in 0..P, g x) = 0
  rw [hz, smul_zero]

end PairFourierTransport
