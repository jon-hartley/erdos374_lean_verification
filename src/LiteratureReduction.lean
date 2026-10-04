import Erdos374_Update152

/-!
This module extends the checked SamplingBoundaryAudit adapter. It exposes
the factorial statement and the eventual counting bound directly.

`LiteratureReduction` and the names below are new project names. The source
seed is unchanged. The two analytic inputs remain explicit parameters;
their derivations from published theorems are in the accompanying note.
-/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace LiteratureReduction

/-- A list of distinct positive factorial indices, with last index m,
whose product is a square in the natural numbers. -/
def SquareFactorialProduct (m k : ℕ) : Prop :=
  ∃ index : Fin k → ℕ,
    StrictMono index ∧
    (∀ i, 1 ≤ index i) ∧
    (∀ i : Fin k, i.val + 1 = k → index i = m) ∧
    ∃ squareRoot : ℕ,
      (∏ i : Fin k, (index i).factorial) = squareRoot ^ 2

/-- The least allowed number of factorial factors is exactly six. -/
def MinimumSix : Set ℕ :=
  {m | 1 < m ∧ SquareFactorialProduct m 6 ∧
    ∀ k : ℕ, 2 ≤ k → k < 6 → ¬ SquareFactorialProduct m k}

theorem hasRep_iff_squareFactorialProduct (m k : ℕ) (hk : 2 ≤ k) :
    Erdos374.HasRep m k ↔ SquareFactorialProduct m k := by
  constructor
  · rintro ⟨_, ⟨representation⟩⟩
    exact ⟨representation.index, representation.increasing,
      representation.positive, representation.endpoint,
      representation.square⟩
  · rintro ⟨index, increasing, positive, endpoint, squareRoot, square⟩
    exact ⟨hk, ⟨{
      index := index
      increasing := increasing
      positive := positive
      endpoint := endpoint
      square := ⟨squareRoot, square⟩
    }⟩⟩

theorem minimumSix_eq_D6 : MinimumSix = Erdos374.D6 := by
  ext m
  constructor
  · rintro ⟨hm, hsix, hshort⟩
    refine ⟨hm, (hasRep_iff_squareFactorialProduct m 6 (by omega)).mpr
      hsix, ?_⟩
    intro k hk hksix hrep
    exact hshort k hk hksix
      ((hasRep_iff_squareFactorialProduct m k hk).mp hrep)
  · rintro ⟨hm, hsix, hshort⟩
    refine ⟨hm, (hasRep_iff_squareFactorialProduct m 6 (by omega)).mp
      hsix, ?_⟩
    intro k hk hksix hrep
    exact hshort k hk hksix
      ((hasRep_iff_squareFactorialProduct m k hk).mpr hrep)

/-- Density supplies a fixed positive fraction at every sufficiently
large cutoff, rather than only infinitely many cutoffs. -/
theorem counting_bound_of_positiveLowerDensity (S : Set ℕ)
    (hS : Erdos374.PositiveLowerDensity S) :
    ∃ c : ℝ, 0 < c ∧ ∃ cutoff : ℕ, ∀ N : ℕ, cutoff ≤ N →
      c * (N : ℝ) ≤ (Erdos374.prefixCount S N : ℝ) := by
  obtain ⟨density, hdensity, hlower⟩ := hS
  obtain ⟨cutoff, hcutoff⟩ := hlower (density / 2) (half_pos hdensity)
  refine ⟨density / 2, half_pos hdensity, max cutoff 1, ?_⟩
  intro N hN
  have hpositive : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hlowerN := hcutoff N (by omega)
  unfold Erdos374.proportion at hlowerN
  have hhalf : density / 2 ≤
      (Erdos374.prefixCount S N : ℝ) / (N : ℝ) := by
    linarith
  exact (le_div_iff₀ hpositive).mp hhalf

theorem positive_lower_density_from_published_interfaces
    (HF : Erdos374.HarmanDyadic151.RealBackwardDyadicExceptionalMeasure151)
    (HS : Erdos374.SamplingPolynomial149.PolynomialReciprocalPrimeSampling) :
    Erdos374.PositiveLowerDensity MinimumSix := by
  rw [minimumSix_eq_D6]
  exact Erdos374.AnalyticClosure151.positive_lower_density_from_backward151
    (Erdos374.HarmanDyadic151.backward_prefix_from_dyadic151 HF) HS

/-- Explicit counting conclusion. HF and HS are mathematical premises,
not proofs supplied by this module. -/
theorem factorial_minimum_six_counting_bound
    (HF : Erdos374.HarmanDyadic151.RealBackwardDyadicExceptionalMeasure151)
    (HS : Erdos374.SamplingPolynomial149.PolynomialReciprocalPrimeSampling) :
    ∃ c : ℝ, 0 < c ∧ ∃ cutoff : ℕ, ∀ N : ℕ, cutoff ≤ N →
      c * (N : ℝ) ≤ (Erdos374.prefixCount MinimumSix N : ℝ) :=
  counting_bound_of_positiveLowerDensity MinimumSix
    (positive_lower_density_from_published_interfaces HF HS)

end LiteratureReduction

#check LiteratureReduction.factorial_minimum_six_counting_bound
#print axioms LiteratureReduction.factorial_minimum_six_counting_bound

run_cmd do
  for target in [
      ``LiteratureReduction.hasRep_iff_squareFactorialProduct,
      ``LiteratureReduction.minimumSix_eq_D6,
      ``LiteratureReduction.counting_bound_of_positiveLowerDensity,
      ``LiteratureReduction.factorial_minimum_six_counting_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "LITERATURE REDUCTION PASSED: HF and HS remain premises"
