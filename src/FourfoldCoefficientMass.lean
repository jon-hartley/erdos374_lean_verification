import BoundedDyadicCoefficients

/-!
Absolute reciprocal mass for a signed divisor family in (A,4A].
The statement uses the original coefficients, with no convolution or
support splitting.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace FourfoldCoefficientMass
open SmoothedDirichletKernel

theorem card_bound (s : Finset ℕ) (A : ℝ) (hA : 1 ≤ A)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) :
    (s.card : ℝ) ≤ 4 * A := by
  have hsub : s ⊆ Finset.Icc 1 ⌊4 * A⌋₊ := by
    intro d hd
    have hdb := hs d hd
    apply Finset.mem_Icc.mpr
    constructor
    · have hh : (1 : ℝ) ≤ d := by linarith [hdb.1]
      exact_mod_cast hh
    · exact (Nat.le_floor_iff (by positivity : 0 ≤ 4 * A)).mpr hdb.2
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hcard : s.card ≤ ⌊4 * A⌋₊ := by omega
  calc
    _ ≤ (⌊4 * A⌋₊ : ℝ) := by exact_mod_cast hcard
    _ ≤ 4 * A := Nat.floor_le (by positivity)

theorem mass_bound (s : Finset ℕ) (A B σ : ℝ) (coeff : ℕ → ℂ)
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hσ : 1 ≤ σ)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A)
    (hcoeff : ∀ d ∈ s, ‖coeff d‖ ≤ B) :
    coefficientMass s coeff σ ≤ 4 * B := by
  have hAp : 0 < A := by linarith
  have hpoint : ∀ d ∈ s,
      ‖coeff d‖ * (d : ℝ) ^ (-σ) ≤ B * A⁻¹ := by
    intro d hd
    have hAd := (hs d hd).1.le
    have hdp : (0 : ℝ) < d := hAp.trans_le hAd
    calc
      _ ≤ B * (d : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right (hcoeff d hd) (by positivity)
      _ ≤ B * A ^ (-σ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hAp hAd (by linarith)) hB
      _ ≤ B * A ^ (-1 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hA (by linarith)) hB
      _ = B * A⁻¹ := by rw [Real.rpow_neg_one]
  calc
    _ ≤ ∑ _d ∈ s, B * A⁻¹ := Finset.sum_le_sum hpoint
    _ = (s.card : ℝ) * (B * A⁻¹) := by simp
    _ ≤ (4 * A) * (B * A⁻¹) :=
      mul_le_mul_of_nonneg_right (card_bound s A hA hs) (by positivity)
    _ = 4 * B := by field_simp

theorem real_weight_mass_bound (s : Finset ℕ) (A B σ : ℝ)
    (weight : ℕ → ℝ) (hA : 1 ≤ A) (hB : 0 ≤ B) (hσ : 1 ≤ σ)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A)
    (hw : ∀ d ∈ s, |weight d| ≤ B) :
    coefficientMass s (fun d => (weight d : ℂ)) σ ≤ 4 * B := by
  apply mass_bound s A B σ (fun d => (weight d : ℂ)) hA hB hσ hs
  intro d hd
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hw d hd

end FourfoldCoefficientMass

#print axioms FourfoldCoefficientMass.real_weight_mass_bound
run_cmd do
  for target in [``FourfoldCoefficientMass.card_bound,
      ``FourfoldCoefficientMass.mass_bound,
      ``FourfoldCoefficientMass.real_weight_mass_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOURFOLD COEFFICIENT MASS PASSED"
