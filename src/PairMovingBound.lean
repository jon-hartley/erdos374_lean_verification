import PairFixedVariance

/-! Unconditional moving-width mean square with a quadratic physical-support
boundary cost and an explicit finite Fourier approximation error. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory

namespace PairMovingBound
open SingletonMoving SingletonHarmonic Erdos374.PairSpacingRational

theorem moving_bound (Q F : ℕ) (a : ℕ → ℝ) (B X H : ℝ)
    (hQ : 1 ≤ Q) (hF : 0 < F) (hB : 0 ≤ B) (hX : 0 < X) (hH : 1 ≤ H)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (1/X)*(∫ x in X..2*X, remainder (Finset.Icc 1 Q) a x (x*H/X)^2) ≤
      B^2*(30*H*harmonicSum Q^3+
        144*H^2*((Q:ℝ)^2/X)*kappa Q F*harmonicSum Q^3+
        48*(Q:ℝ)*harmonicSum Q/F+96*H*(Q:ℝ)^2/((F:ℝ)*X)) := by
  have hS0 := harmonicSum_nonneg Q
  have hS1 := one_le_harmonicSum hQ
  have hH0 : 0 ≤ H := by linarith
  have hF0 : (0:ℝ) < F := by exact_mod_cast hF
  have hκ : 0 ≤ kappa Q F :=
    (Erdos374.PairSpacingHarmonic.H_nonneg _).trans
      (harmonic_image_le_kappa (representatives Q F) Finset.Subset.rfl)
  have hf := PairFixedVariance.fixed_bound Q F B hQ hF hB
  have hm := PairMovingKernel.moving_bound Q a B
    (2*harmonicSum Q^3) (8*harmonicSum Q^3*(Q:ℝ)^2*kappa Q F)
    (8*(Q:ℝ)*harmonicSum Q/F) (8*(Q:ℝ)^2/F) X H hf
    (by positivity) (by positivity) (by positivity) hX hH ha
  have hS23 : harmonicSum Q^2 ≤ harmonicSum Q^3 := by
    nlinarith [mul_nonneg (sq_nonneg (harmonicSum Q)) (sub_nonneg.mpr hS1)]
  have hS3 : 0 ≤ harmonicSum Q^3 := pow_nonneg hS0 3
  have hHS : harmonicSum Q^3 ≤ H*harmonicSum Q^3 := by nlinarith
  have hmain : (6*H+3)*(2*harmonicSum Q^3)+12*harmonicSum Q^2 ≤
      30*H*harmonicSum Q^3 := by nlinarith
  have hbd : (2*H/X)*((6*H+3)*(8*harmonicSum Q^3*(Q:ℝ)^2*kappa Q F)) ≤
      144*H^2*((Q:ℝ)^2/X)*kappa Q F*harmonicSum Q^3 := by
    calc
      _ ≤ (2*H/X)*((9*H)*(8*harmonicSum Q^3*(Q:ℝ)^2*kappa Q F)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  apply hm.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
  calc
    _ = ((6*H+3)*(2*harmonicSum Q^3)+12*harmonicSum Q^2)+
        (2*H/X)*((6*H+3)*(8*harmonicSum Q^3*(Q:ℝ)^2*kappa Q F))+
        48*(Q:ℝ)*harmonicSum Q/F+96*H*(Q:ℝ)^2/((F:ℝ)*X) := by ring
    _ ≤ _ := by linarith only [hmain,hbd]

end PairMovingBound
