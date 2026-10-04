import FlatCofactorContour
import DyadicCoefficientEnergyMass
import RapidPerronParameters

/-!
A relative power saving for the actual low-frequency cofactor replacement.
The remaining polynomial enters through its coefficient energy. No prime
main term or estimate for the continuous contour is assumed or asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace CofactorPowerError
open Erdos374.HarmanGram152 FlatCofactorContour SmoothedWindowTransfer
open SmoothedDirichletKernel

theorem spatial_power_bound (X x : ℝ) (hX : Real.exp 1 ≤ X)
    (hx : x ∈ Icc X (2 * X)) :
    x ^ (1 + 1 / Real.log X) ≤ 4 * X * Real.exp 1 := by
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hσ : 0 ≤ 1 + 1 / Real.log X := by positivity
  have hσtwo : 1 + 1 / Real.log X ≤ 2 := by
    have hh : 1 / Real.log X ≤ 1 := (div_le_one (by linarith)).mpr hlog
    linarith
  calc
    _ ≤ (2 * X) ^ (1 + 1 / Real.log X) :=
      Real.rpow_le_rpow (hXp.le.trans hx.1) hx.2 hσ
    _ = (2 : ℝ) ^ (1 + 1 / Real.log X) * X ^ (1 + 1 / Real.log X) :=
      Real.mul_rpow (by norm_num) hXp.le
    _ ≤ (2 : ℝ) ^ (2 : ℝ) * X ^ (1 + 1 / Real.log X) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hσtwo) (by positivity)
    _ = _ := by
      rw [RapidPerronParameters.vertical_power X hXp (by linarith)]
      norm_num
      ring

theorem eventually_bound (ell : ℝ) (hell : 0 < ell) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (K lo hi M : ℕ) (s : Finset ℕ) (coeff : ℕ → ℂ) (ε x Y H : ℝ),
        X ^ ell ≤ (K : ℝ) → K ≤ lo → lo < hi → 1 ≤ M →
        (∀ n ∈ s, M < n ∧ n ≤ 2 * M) →
        (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ X ^ (ell / 4) * M →
        ε ∈ Ioo 0 1 → x ∈ Icc X (2 * X) → 0 ≤ Y → Y < X →
        1 ≤ H → H ≤ (K : ℝ) ^ (1 / 4 : ℝ) →
        ‖transform
            (fun t => verticalDirichlet152 s coeff (1 + 1 / Real.log X) t *
              verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1)
                (1 + 1 / Real.log X) t)
            MellinSmoothingFunction.smoothing ε (-H) H
              (1 + 1 / Real.log X) (Y / X) x -
          transform
            (fun t => verticalDirichlet152 s coeff (1 + 1 / Real.log X) t *
              continuousPolynomial lo hi (1 + 1 / Real.log X) t)
            MellinSmoothingFunction.smoothing ε (-H) H
              (1 + 1 / Real.log X) (Y / X) x‖ ≤ Y * X ^ (-ell / 4) := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound
    (128 * Real.exp 1) (ell / 8) (by positivity) (by positivity),
    eventually_ge_atTop (Real.exp 1)] with X hconstant hX
  refine ⟨hX, ?_⟩
  intro K lo hi M s coeff ε x Y H hKlow hlo hhi hM hs he hε hx hY hYX hH hHK
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hXone : 1 ≤ X := hconstant.1
  have hK : 1 ≤ K := by exact_mod_cast (Real.one_le_rpow hXone hell.le).trans hKlow
  have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hσ : 1 < 1 + 1 / Real.log X := by
    have hh : 0 < 1 / Real.log X := by positivity
    linarith
  have hσtwo : 1 + 1 / Real.log X ≤ 2 := by
    have hh : 1 / Real.log X ≤ 1 := (div_le_one (by linarith)).mpr hlog
    linarith
  have hpos : ∀ n ∈ s, 0 < n := by
    intro n hn
    have hh := (hs n hn).1
    omega
  have hmass : coefficientMass s coeff (1 + 1 / Real.log X) ≤ X ^ (ell / 8) := by
    simpa only [show ell / 4 / 2 = ell / 8 by ring] using
      DyadicCoefficientEnergyMass.rpow_bound s M coeff
        (1 + 1 / Real.log X) X (ell / 4) hM hσ.le hXp hs he
  have hKpower : (K : ℝ) ^ (-1 / 2 : ℝ) ≤ X ^ (-ell / 2) := by
    calc
      _ ≤ (X ^ ell) ^ (-1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hKlow (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hXp.le]; congr 1; ring
  have hnorm := quarter_cutoff_bound K lo hi s coeff ε (1 + 1 / Real.log X)
    (Y / X) x H hK hlo hhi hpos hε hσ hσtwo (hXp.trans_le hx.1)
    (div_nonneg hY hXp.le) ((div_lt_one hXp).mpr hYX) hH hHK
  have hmnonneg := mass_nonnegative s coeff (1 + 1 / Real.log X)
  have hxp : 0 < x := hXp.trans_le hx.1
  have hspatial := spatial_power_bound X x hX hx
  apply hnorm.trans
  calc
    _ ≤ 32 * X ^ (ell / 8) * (Y / X) * (4 * X * Real.exp 1) *
        X ^ (-ell / 2) := by
      gcongr
    _ = Y * (128 * Real.exp 1) * (X ^ (ell / 8) * X ^ (-ell / 2)) := by
      field_simp
      ring
    _ ≤ Y * X ^ (ell / 8) * (X ^ (ell / 8) * X ^ (-ell / 2)) := by
      gcongr
      exact hconstant.2
    _ = _ := by
      rw [← mul_assoc, mul_assoc Y, ← Real.rpow_add hXp,
        mul_assoc Y, ← Real.rpow_add hXp]
      congr 2
      ring

end CofactorPowerError

#print axioms CofactorPowerError.eventually_bound
run_cmd do
  for target in [``CofactorPowerError.spatial_power_bound,
      ``CofactorPowerError.eventually_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "COFACTOR POWER ERROR PASSED"
