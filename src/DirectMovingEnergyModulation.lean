import DirectMovingEnergyBase

/-! Scalar modulation bounds for the collected energy split. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos374.DirectMovingEnergy
open PairSpacingKernel

theorem norm_modulation (ξ h : ℝ) :
    ‖modulation ξ h‖ = 2 * |Real.sin (Real.pi*ξ*h)| := by
  rw [modulation_exp, norm_sub_rev]
  have he : (-2*Real.pi*Complex.I*ξ*h : ℂ) =
      Complex.I * ((-2*Real.pi*ξ*h : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hx : (-2*Real.pi*ξ*h)/2 = -(Real.pi*ξ*h) := by ring
  rw [hx, Real.sin_neg, Real.norm_eq_abs, abs_mul, abs_neg]
  norm_num

theorem norm_frequency (ξ : ℝ) :
    ‖(2*Real.pi*Complex.I*ξ : ℂ)‖ = 2*Real.pi*|ξ| := by
  simp only [norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]

theorem low_modulation_bound (ξ H : ℝ) (hH : 0 < H)
    (hξ : |ξ| ≤ 1/(4*H)) :
    H * ‖(2*Real.pi*Complex.I*ξ : ℂ)‖ ≤ 2 * ‖modulation ξ H‖ := by
  have habs : |Real.pi*ξ*H| = Real.pi*|ξ| *H := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hH]
  have hh : |ξ| *(4*H) ≤ 1 := (le_div_iff₀ (by positivity)).mp hξ
  have hangle : |Real.pi*ξ*H| ≤ Real.pi/2 := by
    rw [habs]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hangle
  rw [habs] at hs
  have hs' : 2*|ξ| *H ≤ |Real.sin (Real.pi*ξ*H)| := by
    convert hs using 1
    field_simp
  rw [norm_frequency, norm_modulation]
  have hp := mul_le_mul_of_nonneg_right Real.pi_le_four (mul_nonneg (abs_nonneg ξ) hH.le)
  nlinarith

theorem two_frequency_integral_error (ω L : ℝ) (hω : ω ≠ 0) :
    |(∫ h in (0:ℝ)..L, ‖1-exponentialKernel ω h‖^2) - 2*L| ≤ 4/|ω| := by
  let S : Finset ℕ := {0,1}
  let a : ℕ → ℂ := fun n => if n=0 then 1 else -1
  let f : ℕ → ℝ := fun n => if n=0 then 0 else ω
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro x hx y hy he
    have hx' : x=0 ∨ x=1 := by simpa [S] using hx
    have hy' : y=0 ∨ y=1 := by simpa [S] using hy
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;>
      simp_all [f]
  have hh := mean_square_error_le S a f 0 L hinj
  norm_num [S, a, f, exponentialSum, kernel_zero, abs_neg, sub_eq_add_neg] at hh ⊢
  convert hh using 1 <;> ring_nf

theorem high_modulation_integral (ξ H : ℝ) (hH : 0 < H)
    (hξ : 1/(4*H) ≤ |ξ|) :
    4*H ≤ ∫ h in (0:ℝ)..4*H, ‖modulation ξ h‖^2 := by
  have hξp : 0 < |ξ| := (by positivity : (0:ℝ)<1/(4*H)).trans_le hξ
  have hω : -(2*Real.pi*ξ) ≠ 0 := neg_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (abs_pos.mp hξp))
  have hh := two_frequency_integral_error (-(2*Real.pi*ξ)) (4*H) hω
  have hw : |-(2*Real.pi*ξ)| = 2*Real.pi*|ξ| := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  have hprod : 1 ≤ |ξ| *(4*H) := (div_le_iff₀ (by positivity)).mp hξ
  have hπ := mul_le_mul_of_nonneg_right Real.two_le_pi (mul_nonneg (abs_nonneg ξ) hH.le)
  have hden : 0 < 2*Real.pi*|ξ| := by positivity
  have hquot : 4/(2*Real.pi*|ξ|) ≤ 4*H := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  rw [hw] at hh
  have hl := (abs_le.mp hh).1
  change 4*H ≤ ∫ h in (0:ℝ)..4*H, ‖1-exponentialKernel (-(2*Real.pi*ξ)) h‖^2
  linarith

run_cmd do
  for decl in [``norm_modulation, ``norm_frequency, ``low_modulation_bound,
      ``two_frequency_integral_error, ``high_modulation_integral] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "LOW SINE AND HIGH INTEGRATED MODULATION BOUNDS"

end Erdos374.DirectMovingEnergy

