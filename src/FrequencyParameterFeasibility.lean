import MellinCofactorCoverage

/-!
Numerical feasibility of one short-window frequency partition below
the exponent 21/200. This is length arithmetic only: the module does
not identify any sieve coefficient family with a three-factor product.
-/

set_option autoImplicit false
noncomputable section
open Filter

namespace FrequencyParameterFeasibility

def e : ℝ := 1 / 500
def theta : ℝ := 51 / 500
def kappa : ℝ := 1 / 10000
def upperExponent : ℝ := 4491 / 5000
def lowerExponent : ℝ := 1 / 10

theorem exponent_checks :
    0 < e ∧ 0 < kappa ∧ theta < 21 / 200 ∧
    e / 10 + upperExponent * (10 / 9) = 4991 / 5000 ∧
    e + upperExponent * (6 / 7) < 7998 / 10000 ∧
    1 - theta + kappa = 8981 / 10000 ∧
    8981 / 10000 < upperExponent ∧
    lowerExponent ≤ 4999 / 40000 := by
  norm_num [e, theta, kappa, upperExponent, lowerExponent]

theorem length_guards (X : ℝ) (K M N : ℕ) (hX : 1 ≤ X)
    (hK : X ^ (4999 / 10000 : ℝ) ≤ K)
    (hM : X ^ (2999 / 10000 : ℝ) ≤ M)
    (hN : X ^ (1999 / 10000 : ℝ) ≤ N) :
    X ^ (e / 10) * (X ^ upperExponent) ^ (10 / 9 : ℝ) ≤
        (K * M * N : ℕ) ∧
      X ^ e * (X ^ upperExponent) ^ (6 / 7 : ℝ) ≤
        max (K * M : ℕ) (M * N : ℕ) ∧
      X ^ (1 - theta + kappa) ≤ X ^ upperExponent ∧
      X ^ lowerExponent ≤ (K : ℝ) ^ (1 / 4 : ℝ) := by
  have hXp : 0 < X := by linarith
  have htotalExponent : (e / 10 + upperExponent * (10 / 9 : ℝ)) ≤
      4999 / 10000 + 2999 / 10000 + 1999 / 10000 := by
    norm_num [e, upperExponent]
  have hpairExponent : (e + upperExponent * (6 / 7 : ℝ)) ≤
      4999 / 10000 + 2999 / 10000 := by
    norm_num [e, upperExponent]
  have hhighExponent : 1 - theta + kappa ≤ upperExponent := by
    norm_num [theta, kappa, upperExponent]
  have hlowExponent : lowerExponent ≤ (4999 / 10000 : ℝ) * (1 / 4) := by
    norm_num [lowerExponent]
  have htotal : X ^ (4999 / 10000 + 2999 / 10000 + 1999 / 10000 : ℝ) ≤
      (K * M * N : ℕ) := by
    rw [Real.rpow_add hXp, Real.rpow_add hXp, Nat.cast_mul, Nat.cast_mul]
    exact mul_le_mul (mul_le_mul hK hM (by positivity) (by positivity))
      hN (by positivity) (by positivity)
  have hpair : X ^ (4999 / 10000 + 2999 / 10000 : ℝ) ≤
      (K * M : ℕ) := by
    rw [Real.rpow_add hXp, Nat.cast_mul]
    exact mul_le_mul hK hM (by positivity) (by positivity)
  constructor
  · rw [← Real.rpow_mul hXp.le, ← Real.rpow_add hXp]
    exact (Real.rpow_le_rpow_of_exponent_le hX htotalExponent).trans htotal
  constructor
  · rw [← Real.rpow_mul hXp.le, ← Real.rpow_add hXp]
    have hmax : (K * M : ℕ) ≤ max (K * M) (M * N) := le_max_left _ _
    exact (Real.rpow_le_rpow_of_exponent_le hX hpairExponent).trans
      (hpair.trans (by exact_mod_cast hmax))
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le hX hhighExponent
  · have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ X ^ (4999 / 10000 : ℝ))
        hK (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_mul hXp.le] at hroot
    exact (Real.rpow_le_rpow_of_exponent_le hX hlowExponent).trans hroot

theorem floor_power_lower (X a δ : ℝ) (hX : 1 ≤ X)
    (_hδ : 0 ≤ δ) (hδa : δ ≤ a) (hlarge : 2 ≤ X ^ δ) :
    X ^ (a - δ) ≤ (⌊X ^ a⌋₊ : ℝ) := by
  have hXp : 0 < X := by linarith
  have hscale : X ^ δ ≤ X ^ a :=
    Real.rpow_le_rpow_of_exponent_le hX hδa
  have hfloor := Nat.lt_floor_add_one (X ^ a)
  have hproduct : X ^ (a - δ) * X ^ δ = X ^ a := by
    rw [← Real.rpow_add hXp]
    congr 1
    ring
  have hnonneg : 0 ≤ X ^ (a - δ) := by positivity
  have htwo := mul_le_mul_of_nonneg_left hlarge hnonneg
  have hfirst : X ^ (a - δ) ≤ X ^ a / 2 := by
    nlinarith [hproduct]
  have hsecond : X ^ a / 2 ≤ X ^ a - 1 := by
    linarith
  have hlast : X ^ a - 1 < (⌊X ^ a⌋₊ : ℝ) := by
    linarith
  exact (hfirst.trans hsecond).trans hlast.le

theorem eventually_integer_scales :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      let A : ℝ := X ^ (1 / 2 : ℝ)
      let K : ℕ := MellinCofactorCoverage.lowerCutoff X A
      let M : ℕ := ⌊X ^ (3 / 10 : ℝ)⌋₊
      let N : ℕ := ⌊X ^ (1 / 5 : ℝ)⌋₊
      X ^ (4999 / 10000 : ℝ) ≤ K ∧
        X ^ (2999 / 10000 : ℝ) ≤ M ∧
        X ^ (1999 / 10000 : ℝ) ≤ N := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound
    32 (1 / 10000 : ℝ) (by norm_num) (by norm_num)] with X hh
  have hX := hh.1
  have hXp : 0 < X := by linarith
  have hA : 0 < X ^ (1 / 2 : ℝ) := by positivity
  have hroot : (32 : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
    hh.2.trans (Real.rpow_le_rpow_of_exponent_le hX (by norm_num))
  have hscale : 32 * X ^ (1 / 2 : ℝ) ≤ X := by
    have htwo : X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) = X := by
      rw [← Real.rpow_add hXp]
      norm_num
    nlinarith [htwo]
  have hKbase := MellinCofactorCoverage.lowerCutoff_scale X
    (X ^ (1 / 2 : ℝ)) hA hscale
  have hK : X ^ (4999 / 10000 : ℝ) ≤
      (MellinCofactorCoverage.lowerCutoff X (X ^ (1 / 2 : ℝ)) : ℝ) := by
    apply le_trans _ hKbase
    apply (le_div_iff₀ (by positivity : 0 < 32 * X ^ (1 / 2 : ℝ))).mpr
    calc
      X ^ (4999 / 10000 : ℝ) * (32 * X ^ (1 / 2 : ℝ)) =
          32 * X ^ (9999 / 10000 : ℝ) := by
        calc
          _ = 32 * (X ^ (4999 / 10000 : ℝ) * X ^ (1 / 2 : ℝ)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hXp]
            congr 1
            norm_num
      _ ≤ X ^ (1 / 10000 : ℝ) * X ^ (9999 / 10000 : ℝ) :=
        mul_le_mul_of_nonneg_right hh.2 (by positivity)
      _ = X := by
        rw [← Real.rpow_add hXp]
        norm_num
  refine ⟨hX, ?_⟩
  dsimp only
  exact ⟨hK,
    by simpa only [show (3 / 10 : ℝ) - 1 / 10000 = 2999 / 10000 by norm_num]
      using floor_power_lower X (3 / 10) (1 / 10000) hX
        (by norm_num) (by norm_num) (by linarith [hh.2]),
    by simpa only [show (1 / 5 : ℝ) - 1 / 10000 = 1999 / 10000 by norm_num]
      using floor_power_lower X (1 / 5) (1 / 10000) hX
        (by norm_num) (by norm_num) (by linarith [hh.2])⟩

theorem eventually_length_guards :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      let A : ℝ := X ^ (1 / 2 : ℝ)
      let K : ℕ := MellinCofactorCoverage.lowerCutoff X A
      let M : ℕ := ⌊X ^ (3 / 10 : ℝ)⌋₊
      let N : ℕ := ⌊X ^ (1 / 5 : ℝ)⌋₊
      X ^ (e / 10) * (X ^ upperExponent) ^ (10 / 9 : ℝ) ≤
          (K * M * N : ℕ) ∧
        X ^ e * (X ^ upperExponent) ^ (6 / 7 : ℝ) ≤
          max (K * M : ℕ) (M * N : ℕ) ∧
        X ^ (1 - theta + kappa) ≤ X ^ upperExponent ∧
        X ^ lowerExponent ≤ (K : ℝ) ^ (1 / 4 : ℝ) := by
  filter_upwards [eventually_integer_scales] with X hh
  refine ⟨hh.1, ?_⟩
  dsimp only at hh ⊢
  exact length_guards X
    (MellinCofactorCoverage.lowerCutoff X (X ^ (1 / 2 : ℝ)))
    ⌊X ^ (3 / 10 : ℝ)⌋₊ ⌊X ^ (1 / 5 : ℝ)⌋₊
    hh.1 hh.2.1 hh.2.2.1 hh.2.2.2

theorem eventually_band_order :
    ∀ᶠ X : ℝ in atTop,
      0 < X ^ lowerExponent ∧
      2 * X ^ lowerExponent ≤ X ^ upperExponent ∧
      X ^ upperExponent ≤ X ∧
      lowerExponent ≤ (4999 / 10000 : ℝ) ∧
      theta < (21 / 200 : ℝ) := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound
    2 (3991 / 5000 : ℝ) (by norm_num) (by norm_num)] with X hh
  have hXp : 0 < X := by linarith [hh.1]
  have hU : 2 * X ^ lowerExponent ≤ X ^ upperExponent := by
    have hsplit : upperExponent = lowerExponent + 3991 / 5000 := by
      norm_num [upperExponent, lowerExponent]
    rw [hsplit, Real.rpow_add hXp]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hh.2
        (by positivity : 0 ≤ X ^ lowerExponent)
  exact ⟨by positivity, hU,
    (Real.rpow_le_rpow_of_exponent_le hh.1
      (by norm_num [upperExponent])).trans_eq (Real.rpow_one X),
    by norm_num [lowerExponent], by norm_num [theta]⟩

end FrequencyParameterFeasibility

#print axioms FrequencyParameterFeasibility.length_guards
run_cmd do
  for target in [``FrequencyParameterFeasibility.exponent_checks,
      ``FrequencyParameterFeasibility.length_guards,
      ``FrequencyParameterFeasibility.floor_power_lower,
      ``FrequencyParameterFeasibility.eventually_integer_scales,
      ``FrequencyParameterFeasibility.eventually_length_guards,
      ``FrequencyParameterFeasibility.eventually_band_order] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FREQUENCY PARAMETER FEASIBILITY PASSED"
