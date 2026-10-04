import Item1ParameterRawMoment
import Item1ParameterGain
import Item1ParameterLoss
import Item1ParameterLossRoot

/-! The uniform bound for the actual polynomial average in the intermediate range. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

namespace Item1ParameterInner
open Item1ParameterCore Item1ParameterChoice Item1ProductPrefixMoment

theorem inner_bound (M n : ℕ) (L : ℝ) (hM : 8 ≤ M)
    (hL : (10:ℝ)^21 ≤ L)
    (hcut : 6*L^(2/3:ℝ)*Real.log L < Real.log (M:ℝ))
    (hlam : 1 ≤ L/Real.log (M:ℝ)) (hn : n ≤ M) :
    ‖U (positiveSet (scale M)) (degree (L/Real.log (M:ℝ))) (scale M)
      ((M:ℝ)+n) ((M:ℝ)^(L/Real.log (M:ℝ)))‖/(scale M:ℝ)^2 ≤
      Real.exp (-Real.log (M:ℝ)/(4000000*(L/Real.log (M:ℝ))^2)) := by
  let m := Real.log (M:ℝ)
  let lam := L/m
  let d := degree lam
  let z := ‖U (positiveSet (scale M)) d (scale M) ((M:ℝ)+n) ((M:ℝ)^lam)‖/
    (scale M:ℝ)^2
  have hm : 0 ≤ m := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hd : 5 ≤ d := Item1ParameterGain.degree_ge_five lam hlam
  have hdlam : (d:ℝ) ≤ 6*lam := Item1ParameterGain.degree_le_six lam hlam
  have hgain := Item1ParameterGain.gain_sub_eta lam hlam
  have hloss := Item1ParameterLoss.rawLoss_le_cutoff d L m hL hcut hlam hd hdlam
  have hraw := Item1ParameterRawMoment.normalized_moment_le_rawLoss d M n lam
    (by omega) hM hlam hn
  have hscaled := mul_le_mul_of_nonneg_right hgain hm
  have harg : rawLoss d m+(etaLoss d-totalGain d lam)*m ≤ -lam^2*m/80 := by
    change lam^2/40 ≤ totalGain d lam-etaLoss d at hgain
    change rawLoss d m ≤ lam^2*m/80 at hloss
    nlinarith
  have hp : 2*momentOrder d*momentOrder d = 32*d^4 := by unfold momentOrder; ring
  have hpow : z^(2*momentOrder d*momentOrder d) ≤ Real.exp (-lam^2*m/80) := by
    rw [hp]
    exact hraw.trans (Real.exp_le_exp.mpr harg)
  exact Item1ParameterLossRoot.moment_root_bound d m lam z hd hm hlam
    (by positivity) hdlam hpow

end Item1ParameterInner

run_cmd do
  for ax in (← Lean.collectAxioms ``Item1ParameterInner.inner_bound) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in inner bound"
  Lean.logInfo "PARAMETER INNER: 1 standard-axiom theorem guard passed."
