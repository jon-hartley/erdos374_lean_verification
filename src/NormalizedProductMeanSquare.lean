import NormalizedProductLevel

/-!
The classical mean square for the same full mixed product used by
NormalizedProductLevel. Its coefficient energy is proved, and its
support length is 4*K*M. This supplies an input to the prospective
fractional-moment argument, not that argument's power-saving conclusion.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace NormalizedProductMeanSquare
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare
open DirichletProductCoefficients NormalizedProductLevel

theorem integral_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (K M : ℕ) (leftSupport rightSupport : Finset ℕ)
      (left right : ℕ → ℂ) (a T A B σ : ℝ),
      1 ≤ K → 1 ≤ M → 0 ≤ T → 0 < A → 0 < B → 1 ≤ σ →
      (∀ n ∈ leftSupport, K < n ∧ n ≤ 2 * K) →
      (∀ n ∈ rightSupport, M < n ∧ n ≤ 2 * M) →
      (∑ n ∈ leftSupport, ‖left n‖ ^ 2) ≤ A * K →
      (∑ n ∈ rightSupport, ‖right n‖ ^ 2) ≤ B * M →
      (∫ t in Icc a (a + T),
        ‖verticalDirichlet152 leftSupport left σ t *
          verticalDirichlet152 rightSupport right σ t‖ ^ 2) ≤
            (T + 4 * (4 * K * M : ℕ) *
              (1 + Real.log (4 * K * M : ℕ))) * energyBudget D K M ε A B := by
  obtain ⟨D, hD, henergy⟩ := NormalizedProductLevel.energy_bound ε hε
  refine ⟨D, hD, ?_⟩
  intro K M leftSupport rightSupport left right a T A B σ
    hK hM hT hA hB hσ hleft hright heleft heright
  let coeff := coefficient leftSupport rightSupport
    (fun n => conj (normalizedCoefficients152 left σ n))
    (fun n => conj (normalizedCoefficients152 right σ n))
  have hbudget : (∑ n ∈ Finset.Ioc (K * M) (4 * K * M), ‖coeff n‖ ^ 2) ≤
      energyBudget D K M ε A B :=
    henergy K M leftSupport rightSupport left right σ A B
      hK hM hσ hA hB hleft hright heleft heright
  have hlength : (1 : ℝ) ≤ (4 * K * M : ℕ) := by
    exact_mod_cast (show 1 ≤ 4 * K * M by nlinarith)
  have hlog : 0 ≤ Real.log (4 * K * M : ℕ) := Real.log_nonneg hlength
  have hfactor : 0 ≤ T + 4 * (4 * K * M : ℕ) *
      (1 + Real.log (4 * K * M : ℕ)) := by positivity
  have hm := dirichlet_mean_square_le151 (Finset.Ioc (K * M) (4 * K * M))
    coeff (4 * K * M) (fun n hn => by
      have hh := Finset.mem_Ioc.mp hn
      exact ⟨by omega, hh.2⟩) a (a + T)
  simp only [add_sub_cancel_left] at hm
  have hnorm (t : ℝ) :
      ‖verticalDirichlet152 leftSupport left σ t *
        verticalDirichlet152 rightSupport right σ t‖ =
      ‖exponentialSum151 (Finset.Ioc (K * M) (4 * K * M)) coeff
        (fun n => Real.log n) t‖ := by
    exact DirichletProductExpansion.normalized_product_norm _ _ _ _ _ _ _
      (fun n hn => by have := (hleft n hn).1; omega)
      (fun n hn => by have := (hright n hn).1; omega)
      (product_support K M hM leftSupport rightSupport hleft hright)
  simp_rw [hnorm]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show a ≤ a + T by linarith)]
  exact hm.trans (mul_le_mul_of_nonneg_left hbudget hfactor)

end NormalizedProductMeanSquare

#print axioms NormalizedProductMeanSquare.integral_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``NormalizedProductMeanSquare.integral_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED PRODUCT MEAN SQUARE PASSED"
