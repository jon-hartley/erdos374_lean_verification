import PairSpacingRationalMeanSquare

/-! Finite polynomial estimates for a directly moving physical interval.
The coefficients remain collected by their actual rational frequency. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos374.DirectMovingPolynomial
open PairSpacingKernel PairSpacingRational

def polynomial (Q F : ℕ) (b : ℝ → ℂ) (x : ℝ) : ℂ :=
  exponentialSum (frequencies Q F) b (fun ξ => 2 * Real.pi * ξ) x

def derivativeCoefficient (b : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * b ξ

theorem continuous_polynomial (Q F : ℕ) (b : ℝ → ℂ) :
    Continuous (polynomial Q F b) := continuous_sum _ _ _

theorem kappa_nonneg (Q F : ℕ) (hQ : 1 ≤ Q) (hF : 1 ≤ F) :
    0 ≤ kappa Q F := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hFr : (1 : ℝ) ≤ F := by exact_mod_cast hF
  have hl : 0 ≤ Real.log (2 * (F : ℝ) * (Q : ℝ)^2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg ((Q : ℝ)-1)])
  unfold kappa
  linarith

theorem scaled_mean_square (Q F : ℕ) (hQ : 1 ≤ Q) (hF : 1 ≤ F)
    (b : ℝ → ℂ) (X t : ℝ) (ht : 1/2 ≤ t) :
    (∫ x in X..2*X, ‖polynomial Q F b (t*x)‖^2) ≤
      (X + 8*(Q : ℝ)^2*kappa Q F) * ∑ ξ ∈ frequencies Q F, ‖b ξ‖^2 := by
  have ht0 : 0 < t := by linarith
  have hK : 0 ≤ 4*(Q : ℝ)^2*kappa Q F :=
    mul_nonneg (by positivity) (kappa_nonneg Q F hQ hF)
  have he : 0 ≤ ∑ ξ ∈ frequencies Q F, ‖b ξ‖^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hi := physical_mean_square Q F hQ b (t*X) (t*X)
  have hend : t*X+t*X = t*(2*X) := by ring
  rw [hend] at hi
  rw [intervalIntegral.integral_comp_mul_left (fun x => ‖polynomial Q F b x‖^2)
    (ne_of_gt ht0), smul_eq_mul]
  change t⁻¹ * (∫ x in t*X..t*(2*X),
    ‖exponentialSum (frequencies Q F) b (fun ξ => 2*Real.pi*ξ) x‖^2) ≤ _
  calc
    _ ≤ t⁻¹ * ((t*X+4*(Q : ℝ)^2*kappa Q F) *
        ∑ ξ ∈ frequencies Q F, ‖b ξ‖^2) :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr ht0.le)
    _ = (X+(4*(Q : ℝ)^2*kappa Q F)/t) *
        ∑ ξ ∈ frequencies Q F, ‖b ξ‖^2 := by field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ he
      apply add_le_add_right
      apply (div_le_iff₀ ht0).mpr
      nlinarith [mul_nonneg hK (show 0 ≤ 2*t-1 by linarith)]

theorem norm_sub_sq_le (u v : ℂ) :
    ‖u-v‖^2 ≤ 2*‖u‖^2+2*‖v‖^2 := by
  have hn := norm_sub_le u v
  have hs := sq_nonneg (‖u‖-‖v‖)
  nlinarith [norm_nonneg (u-v), norm_nonneg u, norm_nonneg v]

theorem motion_mean_square (Q F : ℕ) (hQ : 1 ≤ Q) (hF : 1 ≤ F)
    (b : ℝ → ℂ) (X α : ℝ) (hX : 0 ≤ X) (hα : 1/2 ≤ α) :
    (∫ x in X..2*X, ‖polynomial Q F b x-polynomial Q F b (α*x)‖^2) ≤
      (4*X+24*(Q : ℝ)^2*kappa Q F) *
        ∑ ξ ∈ frequencies Q F, ‖b ξ‖^2 := by
  have hc := continuous_polynomial Q F b
  have hd : Continuous (fun x => polynomial Q F b (α*x)) :=
    hc.comp (continuous_const.mul continuous_id)
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : X ≤ 2*X)
    (((hc.sub hd).norm.pow 2).intervalIntegrable _ _)
    ((((hc.norm.pow 2).const_mul 2).add ((hd.norm.pow 2).const_mul 2)).intervalIntegrable _ _)
    (fun x _ => norm_sub_sq_le _ _)
  have hx := physical_mean_square Q F hQ b X X
  rw [show X+X=2*X by ring] at hx
  have ha := scaled_mean_square Q F hQ hF b X α hα
  simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply] at hi
  rw [intervalIntegral.integral_add
    (f := fun x => 2*‖polynomial Q F b x‖^2)
    (g := fun x => 2*‖polynomial Q F b (α*x)‖^2)
    (((hc.norm.pow 2).const_mul 2).intervalIntegrable _ _)
    (((hd.norm.pow 2).const_mul 2).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  change (∫ x in X..2*X, ‖polynomial Q F b x‖^2) ≤ _ at hx
  nlinarith

theorem kernel_scale (ω t x : ℝ) :
    exponentialKernel ω (t*x) = exponentialKernel (ω*x) t := by
  unfold exponentialKernel
  congr 1
  push_cast
  ring

theorem kernel_motion_integral (ω x α : ℝ) (hx : x ≠ 0) :
    exponentialKernel ω x-exponentialKernel ω (α*x) =
      (x : ℂ) * ∫ t in α..1,
        (Complex.I * (ω : ℂ)) * exponentialKernel ω (t*x) := by
  by_cases hω : ω = 0
  · simp [hω, kernel_zero]
  simp_rw [kernel_scale]
  rw [intervalIntegral.integral_const_mul,
    integral_kernel (ω*x) α 1 (mul_ne_zero hω hx)]
  have h1 : exponentialKernel (ω*x) 1 = exponentialKernel ω x := by
    simpa only [one_mul] using (kernel_scale ω 1 x).symm
  rw [h1, ← kernel_scale]
  push_cast
  have hcω : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
  have hcx : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  field_simp

theorem polynomial_motion_integral (Q F : ℕ) (b : ℝ → ℂ)
    (x α : ℝ) (hx : x ≠ 0) :
    polynomial Q F b x-polynomial Q F b (α*x) =
      (x : ℂ) * ∫ t in α..1, polynomial Q F (derivativeCoefficient b) (t*x) := by
  unfold polynomial exponentialSum derivativeCoefficient
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [show (fun t : ℝ => (Complex.I * ((2*Real.pi*ξ : ℝ) : ℂ) * b ξ) *
          exponentialKernel (2*Real.pi*ξ) (t*x)) =
        (fun t => b ξ * ((Complex.I * ((2*Real.pi*ξ : ℝ) : ℂ)) *
          exponentialKernel (2*Real.pi*ξ) (t*x))) by funext t; ring,
      intervalIntegral.integral_const_mul, ← mul_sub]
    rw [kernel_motion_integral (2*Real.pi*ξ) x α hx]
    ring
  · intro ξ hξ
    exact (continuous_const.mul ((continuous_kernel _).comp
      (continuous_id.mul continuous_const))).intervalIntegrable _ _

run_cmd do
  for decl in [``polynomial, ``derivativeCoefficient, ``continuous_polynomial,
    ``kappa_nonneg, ``scaled_mean_square, ``norm_sub_sq_le, ``motion_mean_square,
    ``kernel_scale, ``kernel_motion_integral, ``polynomial_motion_integral] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "DIRECT MOVING POLYNOMIAL CHECKED"

end Erdos374.DirectMovingPolynomial
