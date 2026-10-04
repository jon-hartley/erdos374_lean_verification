import PairSpacingPolynomial
import PairMovingKernel

/-! The unconditional finite-frequency fixed-width divisor variance. The
polynomial energy and approximation error are both proved for the literal
signed floor remainder. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace PairFixedVariance
open SingletonHarmonic Erdos374.PairSpacingRational PairFourierApproximation

theorem norm_split (z w : ℂ) : ‖z‖^2 ≤ 2*‖w‖^2+2*‖z-w‖^2 := by
  have ht : ‖z‖ ≤ ‖w‖+‖z-w‖ := by
    calc
      _ = ‖w+(z-w)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le w (z-w)
  have hs := pow_le_pow_left₀ (norm_nonneg z) ht 2
  nlinarith [sq_nonneg (‖w‖-‖z-w‖)]

theorem integral_split (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) (F : ℕ)
    (t T : ℝ) (hT : 0 ≤ T) :
    (∫ x in t..t+T, SingletonResidueVariance.remainder Q a x h^2) ≤
      2*(∫ x in t..t+T, ‖polynomial Q a h F x‖^2)+
      2*(∫ x in t..t+T,
        ‖PairProjectionEnergy.remainder Q a h x-polynomial Q a h F x‖^2) := by
  have hiP : IntervalIntegrable (fun x => ‖polynomial Q a h F x‖^2) volume t (t+T) :=
    ((polynomial_continuous Q a h F).norm.pow 2).intervalIntegrable _ _
  have hiE := difference_square_integrable Q a h F t (t+T)
  calc
    _ ≤ ∫ x in t..t+T, 2*‖polynomial Q a h F x‖^2+
        2*‖PairProjectionEnergy.remainder Q a h x-polynomial Q a h F x‖^2 := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (SingletonResidueVariance.square_intervalIntegrable Q a h t (t+T))
        ((hiP.const_mul 2).add (hiE.const_mul 2))
      intro x _
      have he := norm_split (PairProjectionEnergy.remainder Q a h x) (polynomial Q a h F x)
      simpa only [PairProjectionEnergy.norm_square] using he
    _ = _ := by
      rw [intervalIntegral.integral_add (hiP.const_mul 2) (hiE.const_mul 2)]
      simp only [intervalIntegral.integral_const_mul]

theorem integral_square_le (Q F : ℕ) (a : ℕ → ℝ) (B h t T : ℝ)
    (hQ : 1 ≤ Q) (hF : 0 < F) (hB : 0 ≤ B) (hh : 0 ≤ h) (hT : 0 ≤ T)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (∫ x in t..t+T, SingletonResidueVariance.remainder Q a x h^2) ≤
      B^2*(2*h*harmonicSum Q^3*T+8*h*harmonicSum Q^3*(Q:ℝ)^2*kappa Q F+
        (8*(Q:ℝ)/F)*(T*harmonicSum Q+Q)) := by
  have hp := Erdos374.PairSpacingPolynomial.polynomial_integral_le Q a B h F hQ hB hh t T hT ha
  have he := integral_error_le Q a h F hF B t T hB hT ha
  apply (integral_split Q a h F t T hT).trans
  calc
    _ ≤ 2*(B^2*h*harmonicSum Q^3*(T+4*(Q:ℝ)^2*kappa Q F))+
        2*((4*B^2*(Q:ℝ)/F)*(T*harmonicSum Q+Q)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num))
        (mul_le_mul_of_nonneg_left he (by norm_num))
    _ = _ := by ring

theorem fixed_bound (Q F : ℕ) (B : ℝ) (hQ : 1 ≤ Q) (hF : 0 < F) (hB : 0 ≤ B) :
    PairMovingKernel.FixedBound Q B (2*harmonicSum Q^3)
      (8*harmonicSum Q^3*(Q:ℝ)^2*kappa Q F)
      (8*(Q:ℝ)*harmonicSum Q/F) (8*(Q:ℝ)^2/F) := by
  intro a ha h t T hh hT
  have hb := integral_square_le Q F a B h t T hQ hF hB hh hT ha
  change (∫ x in t..t+T, SingletonMoving.remainder (Finset.Icc 1 Q) a x h^2) ≤ _ at hb
  convert hb using 1
  ring

end PairFixedVariance
