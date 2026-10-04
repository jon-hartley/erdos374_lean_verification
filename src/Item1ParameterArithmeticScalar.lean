import Item1ArithmeticLogBound

/-! Scalar bounds for the actual capped arithmetic majorant. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Item1ParameterArithmeticScalar
open Item1ArithmeticLogBound

theorem arithmeticBound_le_scalar_log (N D : ℕ) (γ R J L W : ℝ)
    (hγ : γ ≠ 0) (hR : 1 ≤ R) (hJ : 1 ≤ J) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hN : (N:ℝ) ≤ R*W) (hD : (D:ℝ) ≤ R*W)
    (hND : (N:ℝ)*(D:ℝ)*|γ| ≤ R^2*W)
    (hinv : 1/|γ| ≤ 8*J*W)
    (hlog : 1+Real.log ((N:ℝ)+1) ≤ L) :
    arithmeticBound N D γ ≤ 100*R^2*J*L*W := by
  have hR0 : 0 ≤ R := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hRR : R ≤ R^2 := by nlinarith
  have hR2 : 1 ≤ R^2 := by nlinarith
  let U := R^2*J*L*W
  have hU1 : 1 ≤ U := by
    calc
      1 = 1*1*1*1 := by norm_num
      _ ≤ U := by dsimp [U]; gcongr
  have hRW : R*W ≤ U := by
    calc
      R*W = R*1*1*W := by ring
      _ ≤ U := by dsimp [U]; gcongr
  have hR2W : R^2*W ≤ U := by
    calc
      R^2*W = R^2*1*1*W := by ring
      _ ≤ U := by dsimp [U]; gcongr
  have hDU : (D:ℝ) ≤ U := hD.trans hRW
  have hNU : (N:ℝ) ≤ U := hN.trans hRW
  have hNDU : (N:ℝ)*(D:ℝ)*|γ| ≤ U := hND.trans hR2W
  have hDL : (D:ℝ)*L ≤ U := by
    calc
      (D:ℝ)*L ≤ (R*W)*L := mul_le_mul_of_nonneg_right hD hL0
      _ = R*1*L*W := by ring
      _ ≤ U := by dsimp [U]; gcongr
  have hIL : (1/|γ|)*L ≤ 8*U := by
    calc
      (1/|γ|)*L ≤ (8*J*W)*L := mul_le_mul_of_nonneg_right hinv hL0
      _ = 8*(1*J*L*W) := by ring
      _ ≤ 8*U := by dsimp [U]; gcongr
  have hmajor : logMajorant N D γ ≤ 100*U := by
    calc
      logMajorant N D γ ≤
          (2*(D:ℝ)+1)+(N:ℝ)*(2*(D:ℝ)*|γ|+2)+2*((D:ℝ)+1/|γ|)*L := by
        unfold logMajorant
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog (by positivity))
      _ ≤ 100*U := by nlinarith only [hDU, hNU, hNDU, hDL, hIL, hU1]
  rw [arithmeticBound, if_neg hγ]
  exact (min_le_right _ _).trans (by simpa only [U, mul_assoc] using hmajor)

theorem arithmeticBound_le_scalar_trivial (N D : ℕ) (γ R J L X : ℝ)
    (hR : 1 ≤ R) (hJ : 1 ≤ J) (hL : 1 ≤ L) (hX : 1 ≤ X)
    (hN : (N:ℝ) ≤ R*X) (hD : (D:ℝ) ≤ R*X) :
    arithmeticBound N D γ ≤ 100*R^2*J*L*X^2 := by
  have hR0 : 0 ≤ R := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hRX : 1 ≤ R*X := one_le_mul_of_one_le_of_one_le hR hX
  have hD3 : 2*(D:ℝ)+1 ≤ 3*(R*X) := by linarith
  have hN2 : (N:ℝ)+1 ≤ 2*(R*X) := by linarith
  calc
    arithmeticBound N D γ ≤ (2*(D:ℝ)+1)*((N:ℝ)+1) :=
      arithmeticBound_le_trivial N D γ
    _ ≤ (3*(R*X))*(2*(R*X)) := mul_le_mul hD3 hN2 (by positivity) (by positivity)
    _ = 6*R^2*X^2 := by ring
    _ ≤ 100*R^2*X^2 := by gcongr; norm_num
    _ = 100*R^2*1*1*X^2 := by ring
    _ ≤ 100*R^2*J*L*X^2 := by gcongr

end Item1ParameterArithmeticScalar

run_cmd do
  for target in [``Item1ParameterArithmeticScalar.arithmeticBound_le_scalar_log,
      ``Item1ParameterArithmeticScalar.arithmeticBound_le_scalar_trivial] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER ARITHMETIC SCALAR: 2 standard-axiom theorem guards passed."
