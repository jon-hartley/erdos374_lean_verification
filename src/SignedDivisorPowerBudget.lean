import SignedDivisorMixedBudget

/-!
Absorb six already established error budgets into one squared spatial
power saving. All six exponents and the resulting c are fixed before X.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter

namespace SignedDivisorPowerBudget

theorem six_power_absorption (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
        ∀ Y : ℝ,
          8 * ((Y * X ^ (-p)) ^ 2 +
              (Y * X ^ (-q)) ^ 2 +
              (Y * X ^ (-r)) ^ 2 +
              (Y * X ^ (-u)) ^ 2 +
              2 * Y ^ 2 * X ^ (-v) +
              2 * Y ^ 2 * X ^ (-w)) ≤
            Y ^ 2 * X ^ (-c) := by
  let m := min p (min q (min r (min u (min v w))))
  have hmpos : 0 < m := by
    dsimp [m]
    exact lt_min hp (lt_min hq (lt_min hr (lt_min hu (lt_min hv hw))))
  have hmp : m ≤ p := min_le_left _ _
  have hmq : m ≤ q := (min_le_right _ _).trans (min_le_left _ _)
  have hmr : m ≤ r :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmu : m ≤ u :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hmv : m ≤ v :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))
  have hmw : m ≤ w :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _))))
  refine ⟨m / 2, by positivity, ?_⟩
  filter_upwards [SpatialErrorBudget.eventually_power_sum m hmpos]
    with X hX
  refine ⟨hX.1, ?_⟩
  intro Y
  have hXp : 0 < X := by linarith [hX.1]
  let Q : ℝ := Y ^ 2 * X ^ (-m)
  have hpower (z : ℝ) (hz : m ≤ z) :
      Y ^ 2 * X ^ (-z) ≤ Q := by
    dsimp [Q]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX.1 (by linarith))
      (sq_nonneg Y)
  have hsquare (z : ℝ) (hz : m ≤ z) :
      (Y * X ^ (-z)) ^ 2 ≤ Q := by
    rw [mul_pow, ← Real.rpow_mul_natCast hXp.le]
    convert hpower (2 * z) (by nlinarith [hmpos, hz]) using 1
    ring
  have h1 := hsquare p hmp
  have h2 := hsquare q hmq
  have h3 := hsquare r hmr
  have h4 := hsquare u hmu
  have h5 := hpower v hmv
  have h6 := hpower w hmw
  apply hX.2 Y
  change 8 * ((Y * X ^ (-p)) ^ 2 +
      (Y * X ^ (-q)) ^ 2 +
      (Y * X ^ (-r)) ^ 2 +
      (Y * X ^ (-u)) ^ 2 +
      2 * Y ^ 2 * X ^ (-v) +
      2 * Y ^ 2 * X ^ (-w)) ≤ 64 * Q
  nlinarith

end SignedDivisorPowerBudget

#print axioms SignedDivisorPowerBudget.six_power_absorption
run_cmd do
  let axioms ← Lean.collectAxioms ``SignedDivisorPowerBudget.six_power_absorption
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice ||
        ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "SIGNED DIVISOR POWER BUDGET PASSED"
