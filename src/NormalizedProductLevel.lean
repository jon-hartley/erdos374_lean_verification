import DirichletProductExpansion
import DyadicLevelParameters

/-!
Large-value measures for the full product of two different normalized
Dirichlet polynomials. Mixed coefficients have support (K*M,4*K*M].
The existing two-block theorem controls that whole support; no individual
block cancellation hypothesis is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal

namespace NormalizedProductLevel
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare
open DirichletProductCoefficients DirichletLargeValueMeasure DyadicLevelParameters

def energyBudget (D : ℝ) (K M : ℕ) (ε A B : ℝ) : ℝ :=
  D * ((4 * K * M : ℕ) : ℝ) ^ ε * (A / K) * (B / M)

theorem normalized_energy (support : Finset ℕ) (N : ℕ) (coeff : ℕ → ℂ)
    (σ A : ℝ) (hN : 1 ≤ N) (hσ : 1 ≤ σ)
    (hs : ∀ n ∈ support, N ≤ n)
    (he : (∑ n ∈ support, ‖coeff n‖ ^ 2) ≤ A * N) :
    (∑ n ∈ support, ‖conj (normalizedCoefficients152 coeff σ n)‖ ^ 2) ≤ A / N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  simp only [RCLike.norm_conj]
  apply (normalized_coefficients_energy152 support coeff N hN σ hσ hs).trans
  calc
    _ ≤ (A * N) / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right he (sq_nonneg _)
    _ = _ := by field_simp

theorem energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (K M : ℕ) (leftSupport rightSupport : Finset ℕ)
      (left right : ℕ → ℂ) (σ A B : ℝ),
      1 ≤ K → 1 ≤ M → 1 ≤ σ → 0 < A → 0 < B →
      (∀ n ∈ leftSupport, K < n ∧ n ≤ 2 * K) →
      (∀ n ∈ rightSupport, M < n ∧ n ≤ 2 * M) →
      (∑ n ∈ leftSupport, ‖left n‖ ^ 2) ≤ A * K →
      (∑ n ∈ rightSupport, ‖right n‖ ^ 2) ≤ B * M →
      (∑ n ∈ Finset.Ioc (K * M) (4 * K * M),
        ‖coefficient leftSupport rightSupport
          (fun n => conj (normalizedCoefficients152 left σ n))
          (fun n => conj (normalizedCoefficients152 right σ n)) n‖ ^ 2) ≤
            energyBudget D K M ε A B := by
  obtain ⟨D, hD, henergy⟩ := DirichletProductCoefficients.energy_bound ε hε
  refine ⟨D, hD, ?_⟩
  intro K M leftSupport rightSupport left right σ A B
    hK hM hσ hA hB hleft hright heleft heright
  have hEL := normalized_energy leftSupport K left σ A hK hσ
    (fun n hn => (hleft n hn).1.le) heleft
  have hER := normalized_energy rightSupport M right σ B hM hσ
    (fun n hn => (hright n hn).1.le) heright
  apply (henergy K M leftSupport rightSupport _ _ hK hM hleft hright).trans
  unfold energyBudget
  gcongr

theorem measure_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (K M : ℕ) (leftSupport rightSupport : Finset ℕ)
      (left right : ℕ → ℂ) (a T A B σ V : ℝ),
      1 ≤ K → 1 ≤ M → 0 ≤ T → 0 < A → 0 < B → 1 ≤ σ → 0 < V →
      (∀ n ∈ leftSupport, K < n ∧ n ≤ 2 * K) →
      (∀ n ∈ rightSupport, M < n ∧ n ≤ 2 * M) →
      (∑ n ∈ leftSupport, ‖left n‖ ^ 2) ≤ A * K →
      (∑ n ∈ rightSupport, ‖right n‖ ^ 2) ≤ B * M →
      let E := energyBudget D K M ε A B
      volume (levelSet (fun t => verticalDirichlet152 leftSupport left σ t *
        verticalDirichlet152 rightSupport right σ t) a T V) ≤
          ENNReal.ofReal (quadratic (K * M) 2 T E / V ^ 2 +
            sextic (K * M) 2 T E / V ^ 6) := by
  obtain ⟨D, hD, henergy⟩ := energy_bound ε hε
  refine ⟨D, hD, ?_⟩
  intro K M leftSupport rightSupport left right a T A B σ V
    hK hM hT hA hB hσ hV hleft hright heleft heright
  have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let weightedLeft := fun n => conj (normalizedCoefficients152 left σ n)
  let weightedRight := fun n => conj (normalizedCoefficients152 right σ n)
  let coeff := coefficient leftSupport rightSupport weightedLeft weightedRight
  let E := energyBudget D K M ε A B
  have hE : 0 < E := by dsimp [E, energyBudget]; positivity
  have hbudget : (∑ n ∈ Finset.Ioc (K * M) (4 * K * M), ‖coeff n‖ ^ 2) ≤ E :=
    henergy K M leftSupport rightSupport left right σ A B
      hK hM hσ hA hB hleft hright heleft heright
  have hnorm (t : ℝ) :
      ‖verticalDirichlet152 leftSupport left σ t *
        verticalDirichlet152 rightSupport right σ t‖ =
      ‖exponentialSum151 (Finset.Ioc (K * M) (4 * K * M)) coeff
        (fun n => Real.log n) t‖ := by
    exact DirichletProductExpansion.normalized_product_norm _ _ _ _ _ _ _
      (fun n hn => by have := (hleft n hn).1; omega)
      (fun n hn => by have := (hright n hn).1; omega)
      (product_support K M hM leftSupport rightSupport hleft hright)
  have hset : levelSet (fun t => verticalDirichlet152 leftSupport left σ t *
        verticalDirichlet152 rightSupport right σ t) a T V =
      levelSet (exponentialSum151 (Finset.Ioc (K * M) (4 * K * M)) coeff
        (fun n => Real.log n)) a T V := by
    ext t
    simp only [levelSet, mem_inter_iff, mem_ofPred_eq, hnorm]
  rw [hset]
  have hprod : 1 ≤ K * M := by nlinarith
  simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num, mul_assoc] using
    DyadicLevelParameters.measure_bound (K * M) 2 coeff a T E V
      hprod (by norm_num) hT hE hV (by
        simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num, mul_assoc] using hbudget)

end NormalizedProductLevel

#print axioms NormalizedProductLevel.measure_bound
run_cmd do
  for target in [``NormalizedProductLevel.energy_bound,
      ``NormalizedProductLevel.measure_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED PRODUCT LEVEL PASSED"
