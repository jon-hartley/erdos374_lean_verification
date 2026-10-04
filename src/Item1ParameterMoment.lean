import Item1ParameterChoice
import Item1ParameterMomentAlgebra

/-! The positive interval moment after division by the averaging size. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

namespace Item1ParameterMoment
open Item1ParameterCore Item1ParameterChoice Item1ProductPrefixMoment
open Item1PrefixNumericalReduction Item1LogPhasePolynomialReduction

theorem positive_interval_moment (d M A n : ℕ) (t : ℝ)
    (hd : 2 ≤ d) (hM : 1 ≤ M) (hA : 1 ≤ A) (hhalf : 2*(A*A) ≤ M) :
    (‖U (positiveSet A) d A ((M:ℝ)+n) t‖/(A:ℝ)^2)^(32*d^4) ≤
      (Salt.Vmvt.vmvtConst d (4*d))^2 *
      (A:ℝ)^(2*Salt.Vmvt.vmvtExp d (4*d)-4*(momentOrder d:ℝ)) *
      numericalProduct d (momentOrder d) (momentOrder d) A A
        (fun j : Fin d => phaseCoefficient ((M:ℝ)+n) t j.val) := by
  let r : ℕ := momentOrder d
  let p : ℕ := 2*r*r
  let q : ℕ := p-2*r
  have hdpos : 0 < d := by omega
  have hrpos : 0 < r := by dsimp [r, momentOrder]; positivity
  have hr : 1 ≤ r := by omega
  have hR : 1 ≤ 4*d := by omega
  have hrd : d*(4*d) = r := by dsimp [r, momentOrder]; ring
  have hsub : 2*r ≤ p := by
    dsimp [p]
    simpa only [mul_one] using Nat.mul_le_mul_left (2*r) hr
  have hq : q+2*r = p := Nat.sub_add_cancel hsub
  have hp : p = 32*d^4 := by dsimp [p, r, momentOrder]; ring
  have hApos : (0:ℝ) < (A:ℝ) := by exact_mod_cast (show 0 < A by omega)
  have h := (Item1VmvtNumericalEndpoint.prefix_and_vmvt_numerical_even_moments_of_positive
    (positiveSet A) (positiveSet_nonempty hA) d M 0 A A (4*d) (4*d) t
    hd hM hA hA
    (fun b hb => ((positiveSet_mem A b).mp hb).1)
    (fun b hb => ((positiveSet_mem A b).mp hb).2) hhalf hR hR).2 n
  have hm : ‖U (positiveSet A) d A ((M:ℝ)+n) t‖^p ≤
      (A:ℝ)^q*(A:ℝ)^q *
      (Salt.Vmvt.vmvtConst d (4*d)*(A:ℝ)^Salt.Vmvt.vmvtExp d (4*d)) *
      (Salt.Vmvt.vmvtConst d (4*d)*(A:ℝ)^Salt.Vmvt.vmvtExp d (4*d)) *
      numericalProduct d r r A A
        (fun j : Fin d => phaseCoefficient ((M:ℝ)+n) t j.val) := by
    simpa only [positiveSet_card, hrd] using h
  have hn := Item1ParameterMomentAlgebra.normalize_moment p q r hApos hq hm
  simpa only [hp] using hn

theorem vmvt_remaining_exponent (d : ℕ) :
    2*Salt.Vmvt.vmvtExp d (4*d)-4*(momentOrder d:ℝ) =
      -(d:ℝ)*((d:ℝ)+1)+3*etaLoss d := by
  unfold Salt.Vmvt.vmvtExp Salt.Vmvt.vmvtEta momentOrder etaLoss
  push_cast
  ring

theorem vmvt_constant_sq (d : ℕ) (hd : 2 ≤ d) :
    (Salt.Vmvt.vmvtConst d (4*d))^2 = Real.exp (192*(d:ℝ)^3*Real.log (d:ℝ)) := by
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
  unfold Salt.Vmvt.vmvtConst Salt.Vmvt.vmvtC0
  rw [← pow_mul, ← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hdpos]
  congr 1
  push_cast
  ring

end Item1ParameterMoment

run_cmd do
  for target in [``Item1ParameterMoment.positive_interval_moment,
      ``Item1ParameterMoment.vmvt_remaining_exponent,
      ``Item1ParameterMoment.vmvt_constant_sq] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER MOMENT: 3 standard-axiom theorem guards passed."
