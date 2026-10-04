import CompactIntegral

/-!
The change of variables x = exp(v), including its Jacobian, for a
weighted square integral. The output retains the explicit endpoint
factor so that later Mellin estimates cannot hide a power of X.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set

namespace LogIntegralTransfer

theorem weighted_bound (X Y σ : ℝ) (hX : 0 < X) (hXY : X ≤ Y)
    (hσ : 0 ≤ σ) (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ x in Icc X Y, x ^ (2 * σ) * ‖F (Real.log x)‖ ^ 2) ≤
      Y ^ (2 * σ + 1) *
        ∫ v in Icc (Real.log X) (Real.log Y), ‖F v‖ ^ 2 := by
  have hY : 0 < Y := hX.trans_le hXY
  have hlogs : Real.log X ≤ Real.log Y := Real.log_le_log hX hXY
  let G : ℝ → ℝ := fun x => x ^ (2 * σ) * ‖F (Real.log x)‖ ^ 2
  have hG : ContinuousOn G
      (Real.exp '' uIcc (Real.log X) (Real.log Y)) := by
    rintro x ⟨v, hv, rfl⟩
    apply ContinuousAt.continuousWithinAt
    exact (continuousAt_id.rpow_const (Or.inl (Real.exp_ne_zero v))).mul
      ((hF.continuousAt.comp (Real.continuousAt_log
        (Real.exp_ne_zero v))).norm.pow 2)
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := Real.log X) (b := Real.log Y)
    (f := Real.exp) (f' := Real.exp) (g := G)
    (fun v _ => Real.hasDerivAt_exp v) Real.continuous_exp.continuousOn hG
  rw [Real.exp_log hX, Real.exp_log hY] at hsub
  have hrewrite (v : ℝ) :
      (G ∘ Real.exp) v * Real.exp v =
        Real.exp v ^ (2 * σ + 1) * ‖F v‖ ^ 2 := by
    dsimp [G]
    rw [Real.log_exp, Real.rpow_add (Real.exp_pos v), Real.rpow_one]
    ring
  simp_rw [hrewrite] at hsub
  have hc : Continuous (fun v => Real.exp v ^ (2 * σ + 1) * ‖F v‖ ^ 2) :=
    (Real.continuous_exp.rpow_const (fun v => Or.inl (Real.exp_ne_zero v))).mul
      (hF.norm.pow 2)
  have hd : Continuous (fun v => Y ^ (2 * σ + 1) * ‖F v‖ ^ 2) :=
    continuous_const.mul (hF.norm.pow 2)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hXY]
  change (∫ x in X..Y, G x) ≤ _
  rw [← hsub]
  calc
    _ ≤ ∫ v in (Real.log X)..(Real.log Y),
        Y ^ (2 * σ + 1) * ‖F v‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on hlogs
        (hc.intervalIntegrable _ _) (hd.intervalIntegrable _ _)
      intro v hv
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply Real.rpow_le_rpow (Real.exp_pos v).le _ (by linarith)
      exact (Real.exp_le_exp.mpr hv.2).trans_eq (Real.exp_log hY)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_of_le hlogs, ← integral_Icc_eq_integral_Ioc]

end LogIntegralTransfer

#print axioms LogIntegralTransfer.weighted_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``LogIntegralTransfer.weighted_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "LOG INTEGRAL TRANSFER PASSED"
