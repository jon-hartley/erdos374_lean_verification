import DirectMovingEnergyPolynomial
import DirectMovingIdentity
import DirectMovingTailAggregate

/-! Direct moving-interval mean square for the literal signed integer-floor
divisor remainder. The boundary term is linear in H. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory

namespace Erdos374.DirectMovingBound
open SingletonHarmonic PairSpacingRational

theorem moving_bound (Q F : ℕ) (a : ℕ → ℝ) (B X H : ℝ)
    (hQ : 1≤Q) (hF : 0<F) (hB : 0≤B) (hX : 0<X)
    (hH : 0<H) (hHX : H≤X/2)
    (ha : ∀n∈Finset.Icc 1 Q, |a n|≤B) :
    (1/X)*(∫x in X..2*X, SingletonMoving.remainder (Finset.Icc 1 Q) a x (x*H/X)^2) ≤
      B^2*(176*H*harmonicSum Q^3*(1+4*(Q:ℝ)^2*kappa Q F/X)+
        32*(Q:ℝ)*harmonicSum Q/F+48*(Q:ℝ)^2/((F:ℝ)*X)) := by
  let R := fun x => PairProjectionEnergy.remainder Q a (x*H/X) x
  let P := fun x => PairFourierApproximation.polynomial Q a (x*H/X) F x
  have hp : (1/X)*(∫x in X..2*X, ‖P x‖^2) ≤
      88*B^2*H*harmonicSum Q^3*(1+4*(Q:ℝ)^2*kappa Q F/X) := by
    simp only [P, DirectMovingIdentity.moving_polynomial_eq]
    exact DirectMovingEnergyPolynomial.base_motion_mean_square Q F hQ
      (Nat.succ_le_iff.mpr hF) a B X H hB hX hH hHX ha
  have he := DirectMovingTailAggregate.moving_error_bound Q F a B X H hF hB hX hHX ha
  have hiP : IntervalIntegrable (fun x => ‖P x‖^2) volume X (2*X) :=
    DirectMovingIdentity.moving_polynomial_square_integrable Q F a X H X (2*X)
  have hiE : IntervalIntegrable (fun x => ‖R x-P x‖^2) volume X (2*X) :=
    DirectMovingTailAggregate.moving_error_square_integrable Q F a X H hX hHX
  have hiR : IntervalIntegrable (fun x => ‖R x‖^2) volume X (2*X) := by
    simp only [R, PairProjectionEnergy.norm_square]
    exact SingletonHarmonicMoving.square_intervalIntegrable_comp (Finset.Icc 1 Q) a
      id (fun x => x*H/X) measurable_id (by fun_prop) X (2*X)
  have hiP2 : IntervalIntegrable (fun x => 2*‖P x‖^2) volume X (2*X) := hiP.const_mul 2
  have hiE2 : IntervalIntegrable (fun x => 2*‖R x-P x‖^2) volume X (2*X) := hiE.const_mul 2
  have ht := intervalIntegral.integral_mono_on (μ := volume)
    (by linarith : X≤2*X) hiR (hiP2.add hiE2)
    (fun x _ => show ‖R x‖^2≤2*‖P x‖^2+2*‖R x-P x‖^2 from by
      have hh := DirectMovingPolynomial.norm_sub_sq_le (P x) (P x-R x)
      rw [show P x-(P x-R x)=R x by ring, norm_sub_rev (P x) (R x)] at hh
      exact hh)
  rw [intervalIntegral.integral_add hiP2 hiE2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at ht
  have hn := mul_le_mul_of_nonneg_left ht (show 0≤1/X by positivity)
  change (1/X)*(∫x in X..2*X, ‖R x-P x‖^2) ≤ _ at he
  have hfinal : (1/X)*(∫x in X..2*X, ‖R x‖^2) ≤
      B^2*(176*H*harmonicSum Q^3*(1+4*(Q:ℝ)^2*kappa Q F/X)+
        32*(Q:ℝ)*harmonicSum Q/F+48*(Q:ℝ)^2/((F:ℝ)*X)) := by
    apply hn.trans
    calc
      _ = 2*((1/X)*(∫x in X..2*X, ‖P x‖^2))+
          2*((1/X)*(∫x in X..2*X, ‖R x-P x‖^2)) := by ring
      _ ≤ 2*(88*B^2*H*harmonicSum Q^3*(1+4*(Q:ℝ)^2*kappa Q F/X))+
          2*(16*B^2*(Q:ℝ)*harmonicSum Q/F+24*B^2*(Q:ℝ)^2/((F:ℝ)*X)) :=
        add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num))
          (mul_le_mul_of_nonneg_left he (by norm_num))
      _ = _ := by ring
  simpa only [R, PairProjectionEnergy.norm_square, SingletonResidueVariance.remainder,
    SingletonMoving.remainder] using hfinal

run_cmd do
  for ax in (←Lean.collectAxioms ``moving_bound) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "ACTUAL SIGNED DIRECT MOVING REMAINDER M2 BOUND PASSED"

end Erdos374.DirectMovingBound
