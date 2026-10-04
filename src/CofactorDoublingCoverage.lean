import MellinCofactorCoverage

/-!
The roomy cofactor endpoints fit inside nine doubling blocks. Both
integer rounding errors are retained. The upper block scale is at
most X once the divisor scale is at least 32.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter

namespace CofactorDoublingCoverage
open MellinCofactorCoverage

def blockCount : ℕ := 9

theorem coverage (X A : ℝ) (hA : 32 ≤ A) (hscale : 32 * A ≤ X) :
    1 ≤ lowerCutoff X A ∧
      upperCutoff X A ≤ 2 ^ blockCount * lowerCutoff X A ∧
      ((2 ^ blockCount * lowerCutoff X A : ℕ) : ℝ) ≤ X := by
  have hAp : 0 < A := by linarith
  have hXp : 0 < X := by linarith
  have hlo := lowerCutoff_scale X A hAp hscale
  have hloOne : (1 : ℝ) ≤ lowerCutoff X A := by
    have hq : (1 : ℝ) ≤ X / (32 * A) := by
      apply (le_div_iff₀ (by positivity : 0 < 32 * A)).mpr
      simpa using hscale
    exact hq.trans hlo
  have hloProd : X ≤ (lowerCutoff X A : ℝ) * (32 * A) :=
    (div_le_iff₀ (by positivity : 0 < 32 * A)).mp hlo
  have hupper : (upperCutoff X A : ℝ) ≤ 8 * X / A + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 8 * X / A)).le
  have hupperProd : ((upperCutoff X A : ℝ) - 1) * A ≤ 8 * X := by
    apply (le_div_iff₀ hAp).mp
    linarith
  have hblock : (upperCutoff X A : ℝ) ≤ 512 * lowerCutoff X A := by
    nlinarith [mul_pos hAp (by norm_num : (0 : ℝ) < 255)]
  have hfloor : (lowerCutoff X A : ℝ) ≤ X / (16 * A) :=
    Nat.floor_le (by positivity)
  have hfloorProd := (le_div_iff₀ (by positivity : 0 < 16 * A)).mp hfloor
  have hscaleUpper : (512 : ℝ) * lowerCutoff X A ≤ X := by
    nlinarith [mul_nonneg (show 0 ≤ A - 32 by linarith)
      (Nat.cast_nonneg (lowerCutoff X A))]
  refine ⟨by exact_mod_cast hloOne, ?_, ?_⟩
  · norm_num [blockCount]
    exact_mod_cast hblock
  · simpa [blockCount] using hscaleUpper

theorem eventual_scales (α ell slack : ℝ)
    (hα : 0 < α) (hell : 0 < ell) (hslack : 0 < slack) :
    ∀ᶠ X : ℝ in atTop, 18 ≤ X ∧
      ∀ A : ℝ, X ^ α ≤ A → A ≤ X ^ (1 - ell - slack) →
        X ^ ell ≤ (lowerCutoff X A : ℝ) ∧
        1 ≤ lowerCutoff X A ∧
        upperCutoff X A ≤ 2 ^ blockCount * lowerCutoff X A ∧
        ((2 ^ blockCount * lowerCutoff X A : ℕ) : ℝ) ≤ X := by
  filter_upwards [eventually_ge_atTop (18 : ℝ),
    PolynomialLogEnvelope.eventually_constant_bound 32 α (by norm_num) hα,
    PolynomialLogEnvelope.eventually_constant_bound 32 slack
      (by norm_num) hslack] with X hX hαpow hslackpow
  refine ⟨hX, ?_⟩
  intro A hAlow hAhigh
  have hA : 32 ≤ A := hαpow.2.trans hAlow
  have hXp : 0 < X := by linarith
  have hAp : 0 < A := by linarith
  have hpowerOne : 1 ≤ X ^ ell := Real.one_le_rpow (by linarith) hell.le
  have hproduct : X ^ ell * (32 * A) ≤ X := by
    calc
      X ^ ell * (32 * A) ≤ X ^ ell * (X ^ slack * X ^ (1 - ell - slack)) := by
        gcongr
        · exact hslackpow.2
      _ = X := by
        rw [← Real.rpow_add hXp, ← Real.rpow_add hXp]
        convert Real.rpow_one X using 1
        ring
  have hscale : 32 * A ≤ X := by
    have hh := mul_le_mul_of_nonneg_right hpowerOne (show 0 ≤ 32 * A by positivity)
    nlinarith
  have hlo : X ^ ell ≤ (lowerCutoff X A : ℝ) :=
    ((le_div_iff₀ (by positivity : 0 < 32 * A)).mpr hproduct).trans
      (lowerCutoff_scale X A hAp hscale)
  have hc := coverage X A hA hscale
  exact ⟨hlo, hc.1, hc.2.1, hc.2.2⟩

end CofactorDoublingCoverage

#print axioms CofactorDoublingCoverage.eventual_scales
run_cmd do
  for target in [``CofactorDoublingCoverage.coverage,
      ``CofactorDoublingCoverage.eventual_scales] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "COFACTOR DOUBLING COVERAGE PASSED"
