import DirichletPowerSupport
import DyadicLevelParameters

/-!
Large-value measures for actual powers of normalized Dirichlet
polynomials. Product coefficients and their energy are proved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal

namespace NormalizedPowerLevel
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare
open DirichletPowerCoefficients DirichletLargeValueMeasure DyadicLevelParameters

def energyBudget (D : ℝ) (N k : ℕ) (ε A : ℝ) : ℝ :=
  D * (2 * (N : ℝ)) ^ ε * (A / N) ^ k

theorem budget_positive (D : ℝ) (N k : ℕ) (ε A : ℝ)
    (hD : 0 < D) (hN : 1 ≤ N) (hA : 0 < A) : 0 < energyBudget D N k ε A := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold energyBudget
  positivity

theorem measure_bound (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (s : Finset ℕ) (N : ℕ) (coeff : ℕ → ℂ) (a T A σ V : ℝ),
      1 ≤ N → 0 ≤ T → 0 < A → 1 ≤ σ → 0 < V →
      (∀ n ∈ s, N < n ∧ n ≤ 2 * N) →
      (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ A * N →
      volume (levelSet (fun t => verticalDirichlet152 s coeff σ t ^ k) a T V) ≤
        ENNReal.ofReal
          (quadratic (N ^ k) k T (energyBudget D N k ε A) / V ^ 2 +
            sextic (N ^ k) k T (energyBudget D N k ε A) / V ^ 6) := by
  obtain ⟨D, hD, hpowerEnergy⟩ := DirichletPowerSupport.energy_bound k hk ε hε
  refine ⟨D, hD, ?_⟩
  intro s N coeff a T A σ V hN hT hA hσ hV hs henergy
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs0 : ∀ n ∈ s, 0 < n := by
    intro n hn
    have hh := (hs n hn).1
    omega
  let weighted : ℕ → ℂ := fun n => conj (normalizedCoefficients152 coeff σ n)
  have he : (∑ n ∈ s, ‖weighted n‖ ^ 2) ≤ A / N := by
    dsimp [weighted]
    simp only [RCLike.norm_conj]
    apply (normalized_coefficients_energy152 s coeff N hN σ hσ
      (fun n hn => (hs n hn).1.le)).trans
    calc
      _ ≤ (A * N) / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right henergy (sq_nonneg _)
      _ = _ := by field_simp
  have hsum : 0 ≤ ∑ n ∈ s, ‖weighted n‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbudget : (∑ n ∈ Finset.Ioc (N ^ k) (2 ^ k * N ^ k),
      ‖coefficient s k weighted n‖ ^ 2) ≤ energyBudget D N k ε A := by
    apply (hpowerEnergy s N weighted hs).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum he k) (by positivity)
  have hnorm (t : ℝ) : ‖verticalDirichlet152 s coeff σ t ^ k‖ =
      ‖exponentialSum151 (Finset.Ioc (N ^ k) (2 ^ k * N ^ k))
        (coefficient s k weighted) (fun n => Real.log n) t‖ := by
    rw [norm_pow, verticalDirichlet_norm152 s coeff σ t hs0, ← norm_pow]
    exact congrArg norm (DirichletPowerSupport.expansion s N k weighted t hk hs)
  have hset : levelSet (fun t => verticalDirichlet152 s coeff σ t ^ k) a T V =
      levelSet (exponentialSum151 (Finset.Ioc (N ^ k) (2 ^ k * N ^ k))
        (coefficient s k weighted) (fun n => Real.log n)) a T V := by
    ext t
    simp only [levelSet, mem_inter_iff, mem_ofPred_eq, hnorm]
  rw [hset]
  exact DyadicLevelParameters.measure_bound (N ^ k) k (coefficient s k weighted)
    a T (energyBudget D N k ε A) V (one_le_pow₀ hN) hk hT
    (budget_positive D N k ε A hD hN hA) hV hbudget

end NormalizedPowerLevel

#print axioms NormalizedPowerLevel.measure_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``NormalizedPowerLevel.measure_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED POWER LEVEL PASSED"
