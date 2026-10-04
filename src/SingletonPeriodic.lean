import SingletonDivisor

/-! An arbitrary interval differs from its periodic average only by a bounded
partial period. This does not yet evaluate the divisor covariance. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set intervalIntegral

namespace SingletonPeriodic

theorem integral_boundary (f : ℝ → ℝ) (P : ℝ) (hP : 0<P)
    (hp : Function.Periodic f P)
    (hi : ∀a b, IntervalIntegrable f volume a b)
    (hb : ∀x, |f x|≤1) (t T : ℝ) :
    |(∫x in t..t+T, f x) - (T/P)*(∫x in 0..P, f x)| ≤ 2*P := by
  let e := Int.fract (T/P)*P
  let q := ⌊T/P⌋
  have he : 0≤e ∧ e<P := by
    constructor
    · exact mul_nonneg (Int.fract_nonneg _) hP.le
    · simpa [e] using mul_lt_mul_of_pos_right (Int.fract_lt_one (T/P)) hP
  have hsplit : e+(q:ℝ)*P=T := by
    simpa only [zsmul_eq_mul] using Int.fract_div_mul_self_add_zsmul_eq P T hP.ne'
  have hpI : (∫x in t+e..t+e+(q:ℝ)*P, f x) =
      (q:ℝ)*(∫x in 0..P, f x) := by
    simpa only [zsmul_eq_mul, zero_add, hp.intervalIntegral_add_eq (t+e) 0] using
      hp.intervalIntegral_add_zsmul_eq q (t+e) hi
  have hadd : (∫x in t..t+T, f x) =
      (∫x in t..t+e, f x) + (q:ℝ)*(∫x in 0..P, f x) := by
    rw [← hpI, integral_add_adjacent_intervals (hi _ _) (hi _ _)]
    congr 1
    linarith [hsplit]
  have hsmall : |∫x in t..t+e, f x| ≤ e := by
    simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg he.1, one_mul]
      using norm_integral_le_of_norm_le_const
        (f:=f) (a:=t) (b:=t+e) (C:=1) (fun x _ => by simpa using hb x)
  have hfull : |∫x in 0..P, f x| ≤ P := by
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hP, one_mul]
      using norm_integral_le_of_norm_le_const
        (f:=f) (a:=0) (b:=P) (C:=1) (fun x _ => by simpa using hb x)
  have hediv : 0≤e/P := div_nonneg he.1 hP.le
  have hedivP : (e/P)*P=e := div_mul_cancel₀ _ hP.ne'
  have hcoeff : (q:ℝ)-T/P = -(e/P) := by
    have hq : (q:ℝ)=(T-e)/P := (eq_div_iff hP.ne').mpr (by linarith [hsplit])
    rw [hq]
    ring
  rw [hadd]
  calc
    _ = |(∫x in t..t+e, f x) - (e/P)*(∫x in 0..P, f x)| := by
      congr 1
      calc
        _ = (∫x in t..t+e, f x) + ((q:ℝ)-T/P)*(∫x in 0..P, f x) := by ring
        _ = _ := by rw [hcoeff]; ring
    _ ≤ |∫x in t..t+e, f x| + |(e/P)*(∫x in 0..P, f x)| := abs_sub _ _
    _ ≤ e + e := by
      apply add_le_add hsmall
      rw [abs_mul, abs_of_nonneg hediv]
      exact (mul_le_mul_of_nonneg_left hfull hediv).trans_eq hedivP
    _ ≤ 2*P := by linarith [he.2]

end SingletonPeriodic
