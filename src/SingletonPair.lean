import SingletonCovariance

/-! The covariance estimate for any two positive divisors on any real interval. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Set intervalIntegral

namespace SingletonPair
open SingletonDivisor SingletonCovariance

theorem discrepancy_scale (g a : ℕ) (hg : 0<g) (ha : 0<a) (x h : ℝ) :
    discrepancy (g*a) ((g:ℝ)*x) h = discrepancy a x (h/g) := by
  have hg0 : (g:ℝ)≠0 := by positivity
  have ha0 : (a:ℝ)≠0 := by positivity
  unfold discrepancy
  push_cast
  rw [show (g:ℝ)*x/((g:ℝ)*a)=x/a by field_simp,
    show ((g:ℝ)*x-h)/((g:ℝ)*a)=(x-h/g)/a by field_simp,
    show h/((g:ℝ)*a)=(h/g)/a by ring]

theorem scaled_integral (g a b : ℕ) (hg : 0<g) (ha : 0<a) (hb : 0<b)
    (hab : a.Coprime b) (h : ℝ) :
    (∫x in (0:ℝ)..(g:ℝ)*a*b,
      discrepancy (g*a) x h * discrepancy (g*b) x h) =
      (g:ℝ)*Int.fract (h/g)*(1-Int.fract (h/g)) := by
  have hs := smul_integral_comp_mul_left
    (a:=(0:ℝ)) (b:=((a*b:ℕ):ℝ))
    (fun x => discrepancy (g*a) x h * discrepancy (g*b) x h) (g:ℝ)
  simp_rw [discrepancy_scale g a hg ha, discrepancy_scale g b hg hb] at hs
  rw [coprime_integral ha hb hab] at hs
  simpa only [smul_eq_mul, mul_zero, Nat.cast_mul, mul_assoc] using hs.symm

theorem scaled_periodic (g a b : ℕ) (hg : 0<g) (ha : 0<a) (hb : 0<b) (h : ℝ) :
    Function.Periodic
      (fun x => discrepancy (g*a) x h * discrepancy (g*b) x h) ((g:ℝ)*a*b) := by
  have h₁ := (periodic (g*a) (Nat.mul_pos hg ha) h).nsmul b
  have h₂ := (periodic (g*b) (Nat.mul_pos hg hb) h).nsmul a
  have h₁' : Function.Periodic (fun x => discrepancy (g*a) x h) ((g:ℝ)*a*b) := by
    simpa only [nsmul_eq_mul, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using h₁
  have h₂' : Function.Periodic (fun x => discrepancy (g*b) x h) ((g:ℝ)*a*b) := by
    simpa only [nsmul_eq_mul, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using h₂
  exact h₁'.mul h₂'

theorem scaled_integral_abs_le (g a b : ℕ) (hg : 0<g) (ha : 0<a) (hb : 0<b)
    (hab : a.Coprime b) (h t T : ℝ) (hh : 0≤h) (hT : 0≤T) :
    |∫x in t..t+T, discrepancy (g*a) x h * discrepancy (g*b) x h| ≤
      T*h/((g:ℝ)*a*b)+2*((g:ℝ)*a*b) := by
  let P : ℝ := (g:ℝ)*a*b
  have hP : 0<P := by dsimp [P]; positivity
  let I : ℝ := ∫x in (0:ℝ)..P, discrepancy (g*a) x h * discrepancy (g*b) x h
  have hI : 0≤I ∧ I≤h := by
    dsimp [I,P]
    rw [scaled_integral g a b hg ha hb hab]
    have hgR : (0:ℝ)<g := by exact_mod_cast hg
    have hu0 := Int.fract_nonneg (h/(g:ℝ))
    have hu1 := Int.fract_lt_one (h/(g:ℝ))
    have huH : Int.fract (h/(g:ℝ)) ≤ h/g := by
      exact sub_le_self _ (Int.cast_nonneg (Int.floor_nonneg.mpr (div_nonneg hh hgR.le)))
    constructor
    · positivity
    · calc
        (g:ℝ)*Int.fract (h/g)*(1-Int.fract (h/g)) ≤ (g:ℝ)*Int.fract (h/g) := by
          nlinarith [mul_nonneg hgR.le hu0]
        _ ≤ (g:ℝ)*(h/g) := mul_le_mul_of_nonneg_left huH hgR.le
        _ = h := by field_simp
  have hboundary := SingletonPeriodic.integral_boundary
    (fun x => discrepancy (g*a) x h * discrepancy (g*b) x h) P hP
    (scaled_periodic g a b hg ha hb h) (product_integrable (g*a) (g*b) h)
    (fun x => product_abs_le (g*a) (g*b) x h) t T
  have hTI : 0≤(T/P)*I := mul_nonneg (div_nonneg hT hP.le) hI.1
  calc
    _ ≤ |(∫x in t..t+T, discrepancy (g*a) x h * discrepancy (g*b) x h)-(T/P)*I| +
        |(T/P)*I| := by
      have ht := abs_add_le
        ((∫x in t..t+T, discrepancy (g*a) x h * discrepancy (g*b) x h)-(T/P)*I)
        ((T/P)*I)
      simpa only [sub_add_cancel] using ht
    _ ≤ 2*P+(T/P)*I := add_le_add hboundary (le_of_eq (abs_of_nonneg hTI))
    _ ≤ 2*P+(T/P)*h := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hI.2 (div_nonneg hT hP.le))
    _ = T*h/((g:ℝ)*a*b)+2*((g:ℝ)*a*b) := by dsimp [P]; ring

theorem integral_abs_le (m n : ℕ) (hm : 0<m) (hn : 0<n) (h t T : ℝ)
    (hh : 0≤h) (hT : 0≤T) :
    |∫x in t..t+T, discrepancy m x h * discrepancy n x h| ≤
      T*h*(Nat.gcd m n:ℝ)/((m:ℝ)*n)+2*(m:ℝ)*n := by
  let g := Nat.gcd m n
  let a := m/g
  let b := n/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left n hm
  have ha : 0<a := Nat.div_gcd_pos_of_pos_left n hm
  have hb : 0<b := by
    dsimp [b,g]
    rw [Nat.gcd_comm]
    exact Nat.div_gcd_pos_of_pos_left m hn
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hg
  have hm' : g*a=m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
  have hn' : g*b=n := Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)
  have ht := scaled_integral_abs_le g a b hg ha hb hab h t T hh hT
  rw [hm',hn'] at ht
  apply ht.trans
  have hgR : (0:ℝ)<g := by exact_mod_cast hg
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have hg1 : (1:ℝ)≤g := by exact_mod_cast hg
  have hmR : (m:ℝ)=(g:ℝ)*a := by exact_mod_cast hm'.symm
  have hnR : (n:ℝ)=(g:ℝ)*b := by exact_mod_cast hn'.symm
  change T*h/((g:ℝ)*a*b)+2*((g:ℝ)*a*b) ≤ T*h*(g:ℝ)/((m:ℝ)*n)+2*(m:ℝ)*n
  rw [hmR,hnR]
  have heq : T*h/((g:ℝ)*a*b)=T*h*(g:ℝ)/(((g:ℝ)*a)*((g:ℝ)*b)) := by field_simp
  rw [heq]
  nlinarith [mul_nonneg (show 0≤(g:ℝ)*a*b by positivity) (sub_nonneg.mpr hg1)]

end SingletonPair
