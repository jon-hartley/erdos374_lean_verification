import SmoothedDirichletKernel
import PolynomialLogEnvelope

/-!
Bound the absolute coefficient mass using a harmonic sum. This supplies
the mass hypothesis of the rapid counting approximation from bounded
weights and finite support, rather than leaving it as an analytic input.
The proof follows polynomial_norm_le and the seed's harmonic estimates.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators

namespace DirichletCoefficientMass
open SmoothedDirichletKernel

theorem harmonic_bound (s : Finset ℕ) (coeff : ℕ → ℂ) (B : ℕ) (σ W : ℝ)
    (hs : ∀ n ∈ s, 0 < n ∧ n ≤ B) (hσ : 1 ≤ σ) (hW : 0 ≤ W)
    (hcoeff : ∀ n ∈ s, ‖coeff n‖ ≤ W) :
    coefficientMass s coeff σ ≤ W * (1 + Real.log (B : ℝ)) := by
  have hterm (n : ℕ) (hn : n ∈ s) :
      ‖coeff n‖ * (n : ℝ) ^ (-σ) ≤ W * (n : ℝ)⁻¹ := by
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (hs n hn).1
    apply mul_le_mul (hcoeff n hn) _ (by positivity) hW
    calc
      _ ≤ (n : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
      _ = _ := by rw [Real.rpow_neg_one]
  have hsub : s ⊆ Finset.Icc 1 B := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(hs n hn).1, (hs n hn).2⟩
  have hsum : ∑ n ∈ Finset.Icc 1 B, (n : ℝ)⁻¹ ≤ 1 + Real.log (B : ℝ) := by
    have hh := harmonic_le_one_add_log B
    rw [harmonic_eq_sum_Icc] at hh
    simpa only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using hh
  calc
    _ ≤ ∑ n ∈ s, W * (n : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.Icc 1 B, W * (n : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = W * ∑ n ∈ Finset.Icc 1 B, (n : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hW

theorem eventual_bound : ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
    ∀ (s : Finset ℕ) (coeff : ℕ → ℂ) (B : ℕ) (σ : ℝ),
      1 ≤ B → (B : ℝ) ≤ X ^ (2 : ℕ) →
      (∀ n ∈ s, 0 < n ∧ n ≤ B) → 1 ≤ σ →
      (∀ n ∈ s, ‖coeff n‖ ≤ X ^ (1 / 200 : ℝ)) →
      coefficientMass s coeff σ ≤ X ^ (1 / 100 : ℝ) := by
  filter_upwards [PolynomialLogEnvelope.eventually_bound 2 1 (1 / 200)
    (by norm_num) (by norm_num)] with X hX
  refine ⟨hX.1, ?_⟩
  intro s coeff B σ hB hBX hs hσ hcoeff
  have hXp : 0 < X := by linarith [hX.1]
  have hBp : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
  have hlog : Real.log (B : ℝ) ≤ 2 * Real.log X := by
    have hh := Real.log_le_log hBp hBX
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX.1
  calc
    _ ≤ X ^ (1 / 200 : ℝ) * (1 + Real.log (B : ℝ)) :=
      harmonic_bound s coeff B σ _ hs hσ (by positivity) hcoeff
    _ ≤ X ^ (1 / 200 : ℝ) * (2 * (1 + Real.log X)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ ≤ X ^ (1 / 200 : ℝ) * X ^ (1 / 200 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [pow_one] using hX.2
    _ = _ := by rw [← Real.rpow_add hXp]; congr 1; norm_num

end DirichletCoefficientMass

#print axioms DirichletCoefficientMass.eventual_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``DirichletCoefficientMass.eventual_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "DIRICHLET COEFFICIENT MASS PASSED"
