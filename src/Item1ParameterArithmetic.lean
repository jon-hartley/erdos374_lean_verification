import Item1ParameterArithmeticScalar
import Item1ParameterArithmeticCoefficient

/-! Bounds on the actual arithmetic factors at the logarithmic Taylor coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace Item1ParameterArithmetic
open Item1ParameterCore Item1ArithmeticLogBound Item1ParameterArithmeticScalar
open Item1ParameterArithmeticCoefficient Item1LogPhasePolynomialReduction
open Item1PrefixNumericalReduction

theorem momentOrder_cast (d : ℕ) : (momentOrder d:ℝ)=4*(d:ℝ)^2 := by
  simp [momentOrder]

theorem logFactor_ge_one (d j : ℕ) (M : ℝ) (hd : 1 ≤ d) (hM : 1 ≤ M) :
    1 ≤ logFactor d j (Real.log M) := by
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdlog : 0 ≤ Real.log (8*(d:ℝ)^2) := Real.log_nonneg (by nlinarith)
  have hMlog : 0 ≤ Real.log M := Real.log_nonneg hM
  have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
  unfold logFactor
  linarith [mul_nonneg hj hMlog]

theorem arithmeticBound_phase_le_factor (d A j : ℕ) (M lam x : ℝ)
    (hM : 8 ≤ M) (_hlam : 1 ≤ lam) (hA : 1 ≤ A)
    (hAM : (A:ℝ) ≤ M^(1/3:ℝ)) (hx : M ≤ x) (hx2 : x ≤ 2*M)
    (hj : 1 ≤ j) (hjd : j ≤ d) :
    arithmeticBound (momentOrder d*A^j) (momentOrder d*A^j)
      (phaseCoefficient x (M^lam) (j-1)/(2*Real.pi)) ≤
      factor d j (Real.log M)*M^(modelExponent lam (j:ℝ)) := by
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  have hd : 1 ≤ d := hj.trans hjd
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hjR : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  have hm0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  let R : ℝ := momentOrder d
  let N : ℕ := momentOrder d*A^j
  let J : ℝ := (j:ℝ)*(2:ℝ)^j
  let L : ℝ := logFactor d j (Real.log M)
  let X : ℝ := M^((j:ℝ)/3)
  let q : ℝ := max ((j:ℝ)/3) (max (lam-(j:ℝ)/3) ((j:ℝ)-lam))
  let W : ℝ := M^q
  let γ : ℝ := phaseCoefficient x (M^lam) (j-1)/(2*Real.pi)
  have hR : 1 ≤ R := by dsimp [R]; rw [momentOrder_cast]; nlinarith
  have hR0 : 0 ≤ R := by linarith
  have hJ : 1 ≤ J :=
    one_le_mul_of_one_le_of_one_le hjR (one_le_pow₀ (by norm_num))
  have hJ0 : 0 ≤ J := by linarith
  have hL : 1 ≤ L := logFactor_ge_one d j M hd hM1
  have hL0 : 0 ≤ L := by linarith
  have hX : 1 ≤ X := Real.one_le_rpow hM1 (by positivity)
  have hX0 : 0 ≤ X := by linarith
  have hqX : (j:ℝ)/3 ≤ q := le_max_left _ _
  have hqY : lam-(j:ℝ)/3 ≤ q :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hqZ : (j:ℝ)-lam ≤ q :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hW : 1 ≤ W := Real.one_le_rpow hM1 (le_trans (by positivity) hqX)
  have hXW : X ≤ W := Real.rpow_le_rpow_of_exponent_le hM1 hqX
  have hYW : M^(lam-(j:ℝ)/3) ≤ W := Real.rpow_le_rpow_of_exponent_le hM1 hqY
  have hZW : M^((j:ℝ)-lam) ≤ W := Real.rpow_le_rpow_of_exponent_le hM1 hqZ
  have hApow : (A:ℝ)^j ≤ X := by
    calc
      (A:ℝ)^j ≤ (M^(1/3:ℝ))^j := pow_le_pow_left₀ (Nat.cast_nonneg A) hAM j
      _ = X := third_power M j hM0.le
  have hN : (N:ℝ) ≤ R*X := by
    dsimp [N]
    push_cast
    exact mul_le_mul_of_nonneg_left hApow hR0
  have hNW : (N:ℝ) ≤ R*W :=
    hN.trans (mul_le_mul_of_nonneg_left hXW hR0)
  have hRX : 1 ≤ R*X := one_le_mul_of_one_le_of_one_le hR hX
  have hNplus : (N:ℝ)+1 ≤ (2*R)*X := by linarith
  have hlog : 1+Real.log ((N:ℝ)+1) ≤ L := by
    calc
      1+Real.log ((N:ℝ)+1) ≤ 1+Real.log ((2*R)*X) :=
        add_le_add le_rfl (Real.log_le_log (by positivity) hNplus)
      _ = 1+Real.log (2*R)+((j:ℝ)/3)*Real.log M := by
        rw [Real.log_mul (by positivity) (by positivity)]
        dsimp [X]
        rw [Real.log_rpow hM0]
        ring
      _ ≤ 1+Real.log (2*R)+(j:ℝ)*Real.log M := by
        gcongr
        linarith
      _ = L := by
        dsimp [L, logFactor]
        rw [show 2*R=8*(d:ℝ)^2 by dsimp [R]; rw [momentOrder_cast]; ring]
  have hX2 : X^2=M^(2*(j:ℝ)/3) := by
    dsimp [X]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le]
    congr 1
    ring
  obtain ⟨hγ, hg, hi⟩ := phaseCoefficient_bounds M lam x j hM1 hx hx2 hj
  have hND : (N:ℝ)*(N:ℝ)*|γ| ≤ R^2*W := by
    calc
      (N:ℝ)*(N:ℝ)*|γ| ≤ (R*X)*(R*X)*M^(lam-(j:ℝ)) := by gcongr
      _ = R^2*(X^2*M^(lam-(j:ℝ))) := by ring
      _ = R^2*M^(lam-(j:ℝ)/3) := by
        rw [hX2, ← Real.rpow_add hM0]
        congr 2
        ring
      _ ≤ R^2*W := mul_le_mul_of_nonneg_left hYW (sq_nonneg R)
  have hinv : 1/|γ| ≤ 8*J*W := by
    calc
      1/|γ| ≤ 8*(j:ℝ)*(2:ℝ)^j*M^((j:ℝ)-lam) := hi
      _ = 8*J*M^((j:ℝ)-lam) := by dsimp [J]; ring
      _ ≤ 8*J*W := mul_le_mul_of_nonneg_left hZW (by positivity)
  have hfac : 100*R^2*J*L=factor d j (Real.log M) := by
    dsimp [R, J, L, factor]
    rw [momentOrder_cast]
    ring
  have htriv := arithmeticBound_le_scalar_trivial N N γ R J L X hR hJ hL hX hN hN
  rw [hfac, hX2] at htriv
  have hlogb := arithmeticBound_le_scalar_log N N γ R J L W hγ hR hJ hL hW
    hNW hNW hND hinv hlog
  rw [hfac] at hlogb
  change arithmeticBound N N γ ≤ factor d j (Real.log M)*M^(min (2*(j:ℝ)/3) q)
  rcases le_total (2*(j:ℝ)/3) q with h | h
  · rw [min_eq_left h]
    exact htriv
  · rw [min_eq_right h]
    exact hlogb

theorem numericalProduct_le_factor_product (d A : ℕ) (M lam x : ℝ)
    (hM : 8 ≤ M) (hlam : 1 ≤ lam) (hA : 1 ≤ A)
    (hAM : (A:ℝ) ≤ M^(1/3:ℝ)) (hx : M ≤ x) (hx2 : x ≤ 2*M) :
    numericalProduct d (momentOrder d) (momentOrder d) A A
      (fun j : Fin d => phaseCoefficient x (M^lam) j.val) ≤
      (∏ j : Fin d, factor d (j.val+1) (Real.log M))*
        M^(∑ j : Fin d, modelExponent lam ((j.val+1:ℕ):ℝ)) := by
  have hM0 : 0 < M := by linarith
  calc
    numericalProduct d (momentOrder d) (momentOrder d) A A
        (fun j : Fin d => phaseCoefficient x (M^lam) j.val) ≤
        ∏ j : Fin d, factor d (j.val+1) (Real.log M)*
          M^(modelExponent lam ((j.val+1:ℕ):ℝ)) := by
      unfold numericalProduct
      apply Finset.prod_le_prod₀
      · intro j _
        exact arithmeticBound_nonneg _ _ _
      · intro j _
        simpa only [Nat.add_sub_cancel] using
          arithmeticBound_phase_le_factor d A (j.val+1) M lam x hM hlam hA hAM hx hx2
            (by omega) (by omega)
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hM0]

end Item1ParameterArithmetic

run_cmd do
  for target in [``Item1ParameterArithmetic.momentOrder_cast,
      ``Item1ParameterArithmetic.logFactor_ge_one,
      ``Item1ParameterArithmetic.arithmeticBound_phase_le_factor,
      ``Item1ParameterArithmetic.numericalProduct_le_factor_product] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER ARITHMETIC: 4 standard-axiom theorem guards passed."
