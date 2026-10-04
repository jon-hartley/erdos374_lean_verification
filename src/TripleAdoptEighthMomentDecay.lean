import TripleAdoptEighthMomentRatio

/-!
Algebraic decay after all moment coefficients and the amplitude-band
count have been bounded by X^(kappa/10).
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace TripleAdoptEighthMomentDecay

def fixedFactor : ℝ := 2 + (2 : ℝ) ^ (8 / 3 : ℝ) * ((2 : ℝ) ^ (2 / 3 : ℝ) + 1)

theorem bound (X N T κ η Q B M J : ℝ)
    (hX : 1 ≤ X) (hκ : 0 < κ) (hκη : κ ≤ η)
    (hN : X ^ η ≤ N) (hT : 0 ≤ T) (hrange : T ^ 2 * (X ^ η) ^ 7 ≤ N ^ 7)
    (hQ : 0 ≤ Q) (hB : 0 < B) (hM : 0 ≤ M) (_hJ : 0 ≤ J)
    (hQbound : Q ≤ X ^ (κ / 10))
    (hBbound : B ≤ X ^ (κ / 10) * T / N ^ 6)
    (hMbound : M ≤ X ^ (κ / 10) * (1 + T / N ^ 3))
    (hJbound : J ≤ X ^ (κ / 10)) :
    (B / X ^ (-κ)) ^ (1 / 5 : ℝ) * M +
      J * (2 : ℝ) ^ (8 / 3 : ℝ) * (Q * (2 : ℝ) ^ (2 / 3 : ℝ) + 1) * X ^ (-κ) ≤
        fixedFactor * X ^ (-κ / 2) := by
  have hXp : 0 < X := by linarith
  have hη : 0 ≤ η := by linarith
  have hZ : 1 ≤ X ^ η := Real.one_le_rpow hX hη
  have hNp : 0 < N := by linarith
  let δ := κ / 10
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδone : 1 ≤ X ^ δ := Real.one_le_rpow hX hδ
  have hμ : 0 < X ^ (-κ) := Real.rpow_pos_of_pos hXp _
  have hratio := TripleAdoptEighthMomentRatio.bound N T (X ^ η) hZ hN hT hrange
  have hbase : (X ^ δ * T / N ^ 6) / X ^ (-κ) = X ^ (δ + κ) * (T / N ^ 6) := by
    calc
      _ = (X ^ δ / X ^ (-κ)) * (T / N ^ 6) := by ring
      _ = _ := by rw [← Real.rpow_sub hXp]; congr 2; ring
  have hfirst : (B / X ^ (-κ)) ^ (1 / 5 : ℝ) * M ≤ 2 * X ^ (-κ / 2) := by
    have hb := Real.rpow_le_rpow (div_nonneg hB.le hμ.le)
      (div_le_div_of_nonneg_right hBbound hμ.le) (by norm_num : (0 : ℝ) ≤ 1 / 5)
    calc
      _ ≤ ((X ^ δ * T / N ^ 6) / X ^ (-κ)) ^ (1 / 5 : ℝ) *
          (X ^ δ * (1 + T / N ^ 3)) := mul_le_mul hb hMbound hM (by positivity)
      _ = X ^ ((6 * δ + κ) / 5) *
          ((T / N ^ 6) ^ (1 / 5 : ℝ) * (1 + T / N ^ 3)) := by
        rw [hbase, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hXp.le]
        rw [show (6 * δ + κ) / 5 = (δ + κ) * (1 / 5) + δ by ring,
          Real.rpow_add hXp]
        ring
      _ ≤ X ^ ((6 * δ + κ) / 5) * (2 / X ^ η) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 2 * X ^ ((6 * δ + κ) / 5 - η) := by
        rw [Real.rpow_sub hXp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX (by dsimp [δ]; linarith)) (by norm_num)
  have hsecond : J * (2 : ℝ) ^ (8 / 3 : ℝ) *
      (Q * (2 : ℝ) ^ (2 / 3 : ℝ) + 1) * X ^ (-κ) ≤
        ((2 : ℝ) ^ (8 / 3 : ℝ) * ((2 : ℝ) ^ (2 / 3 : ℝ) + 1)) * X ^ (-κ / 2) := by
    have hbracket : Q * (2 : ℝ) ^ (2 / 3 : ℝ) + 1 ≤
        X ^ δ * ((2 : ℝ) ^ (2 / 3 : ℝ) + 1) := by
      have hh := mul_le_mul_of_nonneg_right hQbound
        (by positivity : 0 ≤ (2 : ℝ) ^ (2 / 3 : ℝ))
      nlinarith
    calc
      _ ≤ X ^ δ * (2 : ℝ) ^ (8 / 3 : ℝ) *
          (X ^ δ * ((2 : ℝ) ^ (2 / 3 : ℝ) + 1)) * X ^ (-κ) := by
        gcongr
      _ = ((2 : ℝ) ^ (8 / 3 : ℝ) * ((2 : ℝ) ^ (2 / 3 : ℝ) + 1)) *
          X ^ (2 * δ - κ) := by
        rw [show 2 * δ - κ = δ + δ + -κ by ring,
          Real.rpow_add hXp, Real.rpow_add hXp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX (by dsimp [δ]; linarith)) (by positivity)
  exact (add_le_add hfirst hsecond).trans_eq (by unfold fixedFactor; ring)

end TripleAdoptEighthMomentDecay

#print axioms TripleAdoptEighthMomentDecay.bound
run_cmd do
  let axioms ← Lean.collectAxioms ``TripleAdoptEighthMomentDecay.bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "EIGHTH MOMENT DECAY PASSED"
