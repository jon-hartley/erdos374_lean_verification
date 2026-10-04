import FrequencyParameterFeasibility
import CofactorDoublingCoverage

/-!
A numeric frequency witness with the actual product divisor scale
A = (floor(X^(3/10)) * floor(X^(1/5)) : ℕ). This is parameter arithmetic,
not an identification of any sieve coefficients.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter

namespace FactoredFrequencyParameters
open FrequencyParameterFeasibility MellinCofactorCoverage

def middleFactor (X : ℝ) : ℕ := ⌊X ^ (3 / 10 : ℝ)⌋₊
def shortFactor (X : ℝ) : ℕ := ⌊X ^ (1 / 5 : ℝ)⌋₊
def divisorScale (X : ℝ) : ℝ :=
  ((middleFactor X * shortFactor X : ℕ) : ℝ)
def cofactorScale (X : ℝ) : ℕ := lowerCutoff X (divisorScale X)

theorem factor_scale_bounds (X : ℝ) (hX : 1 ≤ X)
    (hM : X ^ (2999 / 10000 : ℝ) ≤ (middleFactor X : ℝ))
    (hN : X ^ (1999 / 10000 : ℝ) ≤ (shortFactor X : ℝ)) :
    X ^ (4998 / 10000 : ℝ) ≤ divisorScale X ∧
      divisorScale X ≤ X ^ (1 / 2 : ℝ) := by
  have hXp : 0 < X := by linarith
  have hMupper : (middleFactor X : ℝ) ≤ X ^ (3 / 10 : ℝ) := by
    exact Nat.floor_le (by positivity)
  have hNupper : (shortFactor X : ℝ) ≤ X ^ (1 / 5 : ℝ) := by
    exact Nat.floor_le (by positivity)
  constructor
  · change X ^ (4998 / 10000 : ℝ) ≤
      ((middleFactor X * shortFactor X : ℕ) : ℝ)
    rw [Nat.cast_mul]
    calc
      _ = X ^ (2999 / 10000 : ℝ) * X ^ (1999 / 10000 : ℝ) := by
        rw [← Real.rpow_add hXp]
        norm_num
      _ ≤ (middleFactor X : ℝ) * (shortFactor X : ℝ) :=
        mul_le_mul hM hN (by positivity) (by positivity)
  · change ((middleFactor X * shortFactor X : ℕ) : ℝ) ≤
      X ^ (1 / 2 : ℝ)
    rw [Nat.cast_mul]
    calc
      _ ≤ X ^ (3 / 10 : ℝ) * X ^ (1 / 5 : ℝ) :=
        mul_le_mul hMupper hNupper (Nat.cast_nonneg _) (by positivity)
      _ = X ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hXp]
        norm_num

theorem eventually_factored_scales :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      32 ≤ divisorScale X ∧
      X ^ (4998 / 10000 : ℝ) ≤ divisorScale X ∧
      divisorScale X ≤ X ^ (1 / 2 : ℝ) ∧
      X ^ (2999 / 10000 : ℝ) ≤ (middleFactor X : ℝ) ∧
      X ^ (1999 / 10000 : ℝ) ≤ (shortFactor X : ℝ) ∧
      X ^ (4999 / 10000 : ℝ) ≤ (cofactorScale X : ℝ) ∧
      1 ≤ cofactorScale X ∧
      upperCutoff X (divisorScale X) ≤
        512 * cofactorScale X ∧
      ((512 * cofactorScale X : ℕ) : ℝ) ≤ X := by
  filter_upwards [FrequencyParameterFeasibility.eventually_integer_scales,
    CofactorDoublingCoverage.eventual_scales
      (4998 / 10000 : ℝ) (4999 / 10000 : ℝ) (1 / 10000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num),
    PolynomialLogEnvelope.eventually_constant_bound
      32 (4998 / 10000 : ℝ) (by norm_num) (by norm_num)]
      with X hscales hcover h32
  have hX : 1 ≤ X := hscales.1
  have hM : X ^ (2999 / 10000 : ℝ) ≤ (middleFactor X : ℝ) := by
    simpa only [middleFactor] using hscales.2.2.1
  have hN : X ^ (1999 / 10000 : ℝ) ≤ (shortFactor X : ℝ) := by
    simpa only [shortFactor] using hscales.2.2.2
  obtain ⟨hAlow, hAupper⟩ := factor_scale_bounds X hX hM hN
  have hAupper' :
      divisorScale X ≤
        X ^ (1 - (4999 / 10000 : ℝ) - (1 / 10000 : ℝ)) := by
    convert hAupper using 1
    norm_num
  have hfour := hcover.2 (divisorScale X) hAlow hAupper'
  have hA32 : 32 ≤ divisorScale X := h32.2.trans hAlow
  refine ⟨hX, hA32, hAlow, hAupper, hM, hN, ?_⟩
  dsimp only [cofactorScale]
  refine ⟨hfour.1, hfour.2.1, ?_, ?_⟩
  · norm_num [CofactorDoublingCoverage.blockCount] at hfour ⊢
    exact hfour.2.2.1
  · norm_num [CofactorDoublingCoverage.blockCount] at hfour ⊢
    exact hfour.2.2.2

theorem eventually_factored_guards :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      let M := middleFactor X
      let N := shortFactor X
      let A := divisorScale X
      let K := cofactorScale X
      32 ≤ A ∧ X ^ (4998 / 10000 : ℝ) ≤ A ∧
        A ≤ X ^ (1 / 2 : ℝ) ∧
        X ^ (4999 / 10000 : ℝ) ≤ K ∧
        1 ≤ K ∧ upperCutoff X A ≤ 512 * K ∧
        ((512 * K : ℕ) : ℝ) ≤ X ∧
        X ^ (FrequencyParameterFeasibility.e / 10) *
          (X ^ upperExponent) ^ (10 / 9 : ℝ) ≤
          (K * M * N : ℕ) ∧
        X ^ FrequencyParameterFeasibility.e *
          (X ^ upperExponent) ^ (6 / 7 : ℝ) ≤
          max (K * M : ℕ) (M * N : ℕ) ∧
        X ^ (1 - theta + kappa) ≤ X ^ upperExponent ∧
        X ^ lowerExponent ≤ (K : ℝ) ^ (1 / 4 : ℝ) ∧
        0 < X ^ lowerExponent ∧
        2 * X ^ lowerExponent ≤ X ^ upperExponent ∧
        X ^ upperExponent ≤ X := by
  filter_upwards [eventually_factored_scales,
    FrequencyParameterFeasibility.eventually_band_order] with X hh hband
  rcases hh with ⟨hX, hA32, hAlow, hAupper, hM, hN,
    hK, hKone, hhi, hKupper⟩
  rcases hband with ⟨hH, hHU, hUX, _, _⟩
  have hlength := FrequencyParameterFeasibility.length_guards X
    (cofactorScale X) (middleFactor X) (shortFactor X)
    hX hK hM hN
  refine ⟨hX, ?_⟩
  dsimp only
  exact ⟨hA32, hAlow, hAupper, hK, hKone, hhi, hKupper,
    hlength.1, hlength.2.1, hlength.2.2.1,
    hlength.2.2.2, hH, hHU, hUX⟩

end FactoredFrequencyParameters

#print axioms FactoredFrequencyParameters.eventually_factored_guards
run_cmd do
  for target in [``FactoredFrequencyParameters.factor_scale_bounds,
      ``FactoredFrequencyParameters.eventually_factored_scales,
      ``FactoredFrequencyParameters.eventually_factored_guards] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice ||
          ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FACTORED FREQUENCY PARAMETERS PASSED"
