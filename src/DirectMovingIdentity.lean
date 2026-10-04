import DirectMovingPolynomial
import DirectMovingEnergyBase
import PairSpacingPolynomial

/-! The original hard projection is exactly the difference of a single
collected base polynomial at its two endpoints. All frequency collisions
and signed coefficients remain present. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos374.DirectMovingIdentity
open PairSpacingKernel PairSpacingRational PairSpacingCollectedEnergy
open DirectMovingEnergy

theorem modulation_kernel (ξ h x : ℝ) :
    modulation ξ h * exponentialKernel (2*Real.pi*ξ) x =
      exponentialKernel (2*Real.pi*ξ) x-exponentialKernel (2*Real.pi*ξ) (x-h) := by
  unfold modulation
  rw [sub_mul, one_mul]
  congr 1
  unfold exponentialKernel
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fixed_polynomial_eq (Q F : ℕ) (a : ℕ → ℝ) (h x : ℝ) :
    PairFourierApproximation.polynomial Q a h F x =
      DirectMovingPolynomial.polynomial Q F (baseCoefficient Q F a) x-
        DirectMovingPolynomial.polynomial Q F (baseCoefficient Q F a) (x-h) := by
  rw [PairSpacingPolynomial.polynomial_eq_collected]
  unfold DirectMovingPolynomial.polynomial exponentialSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [coefficient_eq_modulation]
  calc
    modulation ξ h * baseCoefficient Q F a ξ * exponentialKernel (2*Real.pi*ξ) x =
        baseCoefficient Q F a ξ * (modulation ξ h * exponentialKernel (2*Real.pi*ξ) x) := by ring
    _ = _ := by rw [modulation_kernel, mul_sub]

theorem moving_polynomial_eq (Q F : ℕ) (a : ℕ → ℝ) (X H x : ℝ) :
    PairFourierApproximation.polynomial Q a (x*H/X) F x =
      DirectMovingPolynomial.polynomial Q F (baseCoefficient Q F a) x-
        DirectMovingPolynomial.polynomial Q F (baseCoefficient Q F a) ((1-H/X)*x) := by
  rw [fixed_polynomial_eq]
  congr 2
  ring

theorem moving_polynomial_continuous (Q F : ℕ) (a : ℕ → ℝ) (X H : ℝ) :
    Continuous (fun x => PairFourierApproximation.polynomial Q a (x*H/X) F x) := by
  have he : (fun x => PairFourierApproximation.polynomial Q a (x*H/X) F x) =
      (fun x => DirectMovingPolynomial.polynomial Q F (baseCoefficient Q F a) x-
        DirectMovingPolynomial.polynomial Q F (baseCoefficient Q F a) ((1-H/X)*x)) :=
    funext (moving_polynomial_eq Q F a X H)
  rw [he]
  have hc := DirectMovingPolynomial.continuous_polynomial Q F (baseCoefficient Q F a)
  exact hc.sub (hc.comp (continuous_const.mul continuous_id))

theorem moving_polynomial_square_integrable (Q F : ℕ) (a : ℕ → ℝ) (X H A B : ℝ) :
    IntervalIntegrable (fun x => ‖PairFourierApproximation.polynomial Q a (x*H/X) F x‖^2)
      volume A B :=
  ((moving_polynomial_continuous Q F a X H).norm.pow 2).intervalIntegrable A B

run_cmd do
  for target in [``modulation_kernel, ``fixed_polynomial_eq, ``moving_polynomial_eq,
      ``moving_polynomial_continuous, ``moving_polynomial_square_integrable] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "DirectMovingIdentity PASSED; 5 declarations guarded; exact original hard projection"
end Erdos374.DirectMovingIdentity
end
