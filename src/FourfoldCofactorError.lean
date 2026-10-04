import FourfoldCoefficientMass
import CofactorPowerError
import MellinCofactorCoverage

/-!
The actual low-frequency flat cofactor error for original signed divisor
weights supported in (A,4A]. The common cofactor endpoints are retained
in the final specialization; no main-term extraction is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace FourfoldCofactorError
open Erdos374.HarmanGram152 SmoothedWindowTransfer
open SmoothedDirichletKernel FlatCofactorContour

theorem eventually_bound (ell : ℝ) (hell : 0 < ell) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (A : ℝ) (K lo hi : ℕ) (s : Finset ℕ) (weight : ℕ → ℝ)
        (ε x Y H : ℝ),
        1 ≤ A →
        (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) →
        (∀ d ∈ s, |weight d| ≤ X ^ (ell / 16)) →
        X ^ ell ≤ (K : ℝ) → K ≤ lo → lo < hi →
        ε ∈ Ioo 0 1 → x ∈ Icc X (2 * X) → 0 ≤ Y → Y < X →
        1 ≤ H → H ≤ (K : ℝ) ^ (1 / 4 : ℝ) →
        ‖transform
            (fun t => verticalDirichlet152 s (fun d => (weight d : ℂ))
                (1 + 1 / Real.log X) t *
              verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1)
                (1 + 1 / Real.log X) t)
            MellinSmoothingFunction.smoothing ε (-H) H
              (1 + 1 / Real.log X) (Y / X) x -
          transform
            (fun t => verticalDirichlet152 s (fun d => (weight d : ℂ))
                (1 + 1 / Real.log X) t *
              continuousPolynomial lo hi (1 + 1 / Real.log X) t)
            MellinSmoothingFunction.smoothing ε (-H) H
              (1 + 1 / Real.log X) (Y / X) x‖ ≤ Y * X ^ (-ell / 4) := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound
    (512 * Real.exp 1) (3 * ell / 16) (by positivity) (by positivity),
    eventually_ge_atTop (Real.exp 1)] with X hconstant hX
  refine ⟨hX, ?_⟩
  intro A K lo hi s weight ε x Y H hA hs hw hKlow hlo hhi hε hx hY hYX hH hHK
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
  have hpos : ∀ d ∈ s, 0 < d := by
    intro d hd
    have hh := (hs d hd).1
    have hh' : (0 : ℝ) < d := by linarith
    exact_mod_cast hh'
  have hmass : coefficientMass s (fun d => (weight d : ℂ))
      (1 + 1 / Real.log X) ≤ 4 * X ^ (ell / 16) :=
    FourfoldCoefficientMass.real_weight_mass_bound s A (X ^ (ell / 16))
      (1 + 1 / Real.log X) weight hA (by positivity) hσ.le hs hw
  have hKpower : (K : ℝ) ^ (-1 / 2 : ℝ) ≤ X ^ (-ell / 2) := by
    calc
      _ ≤ (X ^ ell) ^ (-1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hKlow (by norm_num)
      _ = X ^ (-ell / 2) := by
        rw [← Real.rpow_mul hXp.le]
        congr 1
        ring
  have hnorm := quarter_cutoff_bound K lo hi s (fun d => (weight d : ℂ))
    ε (1 + 1 / Real.log X) (Y / X) x H hK hlo hhi hpos hε hσ hσtwo
    (hXp.trans_le hx.1) (div_nonneg hY hXp.le)
    ((div_lt_one hXp).mpr hYX) hH hHK
  have hspatial := CofactorPowerError.spatial_power_bound X x hX hx
  have hxpow_nonneg : 0 ≤ x ^ (1 + 1 / Real.log X) := by
    exact Real.rpow_nonneg (hXp.le.trans hx.1) _
  apply hnorm.trans
  calc
    _ ≤ 32 * (4 * X ^ (ell / 16)) * (Y / X) *
        (4 * X * Real.exp 1) * X ^ (-ell / 2) := by
          gcongr
    _ = Y * (512 * Real.exp 1) *
        (X ^ (ell / 16) * X ^ (-ell / 2)) := by
          field_simp
          ring
    _ ≤ Y * X ^ (3 * ell / 16) *
        (X ^ (ell / 16) * X ^ (-ell / 2)) := by
          gcongr
          exact hconstant.2
    _ = Y * X ^ (-ell / 4) := by
      rw [mul_assoc, ← Real.rpow_add hXp, ← Real.rpow_add hXp]
      congr 1
      ring

theorem eventually_common_cofactor (ell : ℝ) (hell : 0 < ell) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (A : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ) (ε x Y H : ℝ),
        1 ≤ A →
        (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) →
        (∀ d ∈ s, |weight d| ≤ X ^ (ell / 16)) →
        X ^ ell ≤
          (MellinCofactorCoverage.lowerCutoff X A : ℝ) →
        ε ∈ Ioo 0 1 → x ∈ Icc X (2 * X) → 0 ≤ Y → Y < X →
        1 ≤ H →
        H ≤ (MellinCofactorCoverage.lowerCutoff X A : ℝ) ^ (1 / 4 : ℝ) →
        ‖transform
            (fun t => verticalDirichlet152 s (fun d => (weight d : ℂ))
                (1 + 1 / Real.log X) t *
              verticalDirichlet152 (MellinCofactorCoverage.cofactors X A)
                (fun _ => 1) (1 + 1 / Real.log X) t)
            MellinSmoothingFunction.smoothing ε (-H) H
              (1 + 1 / Real.log X) (Y / X) x -
          transform
            (fun t => verticalDirichlet152 s (fun d => (weight d : ℂ))
                (1 + 1 / Real.log X) t *
              continuousPolynomial (MellinCofactorCoverage.lowerCutoff X A)
                (MellinCofactorCoverage.upperCutoff X A)
                (1 + 1 / Real.log X) t)
            MellinSmoothingFunction.smoothing ε (-H) H
              (1 + 1 / Real.log X) (Y / X) x‖ ≤ Y * X ^ (-ell / 4) := by
  filter_upwards [eventually_bound ell hell] with X hh
  refine ⟨hh.1, ?_⟩
  intro A s weight ε x Y H hA hs hw hKlow hε hx hY hYX hH hHK
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hh.1
  have hAp : 0 < A := by linarith
  have hstrict := MellinCofactorCoverage.cutoff_strict X A hXp hAp
  exact hh.2 A (MellinCofactorCoverage.lowerCutoff X A)
    (MellinCofactorCoverage.lowerCutoff X A)
    (MellinCofactorCoverage.upperCutoff X A)
    s weight ε x Y H hA hs hw hKlow le_rfl hstrict
    hε hx hY hYX hH hHK

end FourfoldCofactorError

#print axioms FourfoldCofactorError.eventually_common_cofactor
run_cmd do
  for target in [``FourfoldCofactorError.eventually_bound,
      ``FourfoldCofactorError.eventually_common_cofactor] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOURFOLD COFACTOR ERROR PASSED"
