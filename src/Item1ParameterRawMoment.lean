import Item1ParameterMoment
import Item1ParameterFloorLoss
import Item1ParameterArithmetic
import Item1ParameterFactorProduct
import Item1ParameterGainSum

/-! All constants and floor losses in the actual normalized moment. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open scoped BigOperators

namespace Item1ParameterRawMoment
open Item1ParameterCore Item1ParameterChoice Item1ParameterMoment
open Item1ParameterFloorLoss Item1ParameterArithmetic Item1ParameterFactorProduct
open Item1ProductPrefixMoment Item1PrefixNumericalReduction Item1LogPhasePolynomialReduction

theorem normalized_moment_le_rawLoss (d M n : ℕ) (lam : ℝ)
    (hd : 2 ≤ d) (hM : 8 ≤ M) (hlam : 1 ≤ lam) (hn : n ≤ M) :
    (‖U (positiveSet (scale M)) d (scale M) ((M:ℝ)+n) ((M:ℝ)^lam)‖ /
      (scale M:ℝ)^2)^(32*d^4) ≤
      Real.exp (rawLoss d (Real.log (M:ℝ)) +
        (etaLoss d-totalGain d lam)*Real.log (M:ℝ)) := by
  let A := scale M
  let m := Real.log (M:ℝ)
  let D : ℝ := (d:ℝ)*((d:ℝ)+1)
  let e : ℝ := -D+3*etaLoss d
  let H : ℝ := (d:ℝ)*Real.log 1600 + 5*(d:ℝ)*Real.log (d:ℝ) +
    (1/2:ℝ)*(d:ℝ)*((d:ℝ)+1)*Real.log 2 + (d:ℝ)*Real.log (logFactor d d m)
  let W : ℝ := ∑ j : Fin d, modelExponent lam ((j.val+1:ℕ):ℝ)
  let Q := numericalProduct d (momentOrder d) (momentOrder d) A A
    (fun j : Fin d => phaseCoefficient ((M:ℝ)+n) ((M:ℝ)^lam) j.val)
  have hM8 : (8:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hMp : (0:ℝ) < (M:ℝ) := by linarith
  have hm : 0 ≤ m := Real.log_nonneg (by linarith)
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hA, hAlower, hAupper, hhalf⟩ := scale_bounds hM
  have hnR : (n:ℝ) ≤ (M:ℝ) := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hnum := numericalProduct_le_factor_product d A (M:ℝ) lam ((M:ℝ)+n)
    hM8 hlam hA hAupper (by linarith) (by linarith)
  have hfac := factor_product_le_exp d m hd1 hm
  have hQ : Q ≤ Real.exp H*(M:ℝ)^W := hnum.trans
    (mul_le_mul_of_nonneg_right hfac (Real.rpow_nonneg hMp.le _))
  have hQ0 : 0 ≤ Q := numericalProduct_nonneg _ _ _ _ _ _
  obtain ⟨he, he0⟩ := remaining_exponent_bounds d hd1
  have hfloor : (A:ℝ)^e ≤ Real.exp (D*Real.log 2+(e/3)*m) :=
    floor_power_loss (M:ℝ) (A:ℝ) D e hMp hAlower
      (by simpa only [e, D, neg_mul] using he)
      (by simpa only [e, D, neg_mul] using he0)
  have hmoment := positive_interval_moment d M A n ((M:ℝ)^lam)
    hd (by omega) hA hhalf
  rw [vmvt_constant_sq d hd, vmvt_remaining_exponent] at hmoment
  calc
    (‖U (positiveSet A) d A ((M:ℝ)+n) ((M:ℝ)^lam)‖/(A:ℝ)^2)^(32*d^4) ≤
        Real.exp (192*(d:ℝ)^3*Real.log (d:ℝ))*(A:ℝ)^e*Q := by
          simpa only [e, D, Q, neg_mul] using hmoment
    _ ≤ Real.exp (192*(d:ℝ)^3*Real.log (d:ℝ))*
        Real.exp (D*Real.log 2+(e/3)*m)*Q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfloor (Real.exp_nonneg _)) hQ0
    _ ≤ Real.exp (192*(d:ℝ)^3*Real.log (d:ℝ))*
        Real.exp (D*Real.log 2+(e/3)*m)*(Real.exp H*(M:ℝ)^W) :=
      mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = Real.exp (rawLoss d (Real.log (M:ℝ)) +
        (etaLoss d-totalGain d lam)*Real.log (M:ℝ)) := by
      rw [Real.rpow_def_of_pos hMp]
      repeat rw [← Real.exp_add]
      congr 1
      dsimp [H, W, e, D, m]
      rw [Item1ParameterGain.sum_modelExponent]
      unfold rawLoss logFactor
      ring

end Item1ParameterRawMoment

run_cmd do
  for ax in (← Lean.collectAxioms ``Item1ParameterRawMoment.normalized_moment_le_rawLoss) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in raw moment"
  Lean.logInfo "PARAMETER RAW MOMENT: 1 standard-axiom theorem guard passed."
