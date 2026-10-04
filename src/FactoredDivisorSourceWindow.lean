import FactoredDivisorVariableFamily
import FactoredDivisorWindowScales

/-!
The source window Y = (1/2) X^(1/10+s) lies in the uniform window range
selected with ε=s/2. The strict exponent margin absorbs its factor 1/2.
These are actual remainder estimates for that window, not monotonicity claims.
-/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace FactoredDivisorVariableWindow
open FactoredDivisorHarmanRegion

theorem eventually_source_region (α ell slack nu s : ℝ)
    (hα : 0 < α) (hell : 0 < ell)
    (hslack : 0 < slack) (hnu : 0 < nu)
    (hs : 0 < s) (hsmall : s < 1 / 100) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
        ∀ (M N : ℕ) (sm sn : Finset ℕ) (am an : ℕ → ℝ),
          let A : ℝ := (M * N : ℕ)
          let Y : ℝ := sourceWindow s X
          1 ≤ M → 1 ≤ N →
          X ^ α ≤ A → A ≤ X ^ (1 - ell - slack) →
          X ^ nu ≤ (N : ℝ) →
          ((N : ℝ) ≤ X ^ (8 / 35 : ℝ) ∨
            X ^ (27 / 35 : ℝ) ≤ A) →
          (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
          (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
          (∀ n ∈ sm, |am n| ≤ 1) →
          (∀ n ∈ sn, |an n| ≤ 1) →
          (1 / X) * (∫ x in Icc X (2 * X),
            HarmanDivisorWindow.remainder
              (FactoredDivisorWeights.support sm sn)
              (FactoredDivisorWeights.coefficient sm sn am an)
              (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  obtain ⟨c, hc, hregion⟩ := FactoredDivisorVariableWindow.eventually_region
    α ell slack nu (s / 2)
    hα hell hslack hnu (by positivity) (by linarith)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hregion, eventual_source_window_guards s hs hsmall]
    with X hr hw
  refine ⟨hr.1, ?_⟩
  intro M N sm sn am an
  exact hr.2 (sourceWindow s X) M N sm sn am an hw.2.1 hw.2.2

theorem eventually_source_bound {ι : Type*} (α ell slack nu s : ℝ)
    (hα : 0 < α) (hell : 0 < ell)
    (hslack : 0 < slack) (hnu : 0 < nu)
    (hs : 0 < s) (hsmall : s < 1 / 100) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
        ∀ (family : Finset ι) (M N : ι → ℕ)
          (sm sn : ι → Finset ℕ) (am an : ι → ℕ → ℝ),
          let Y : ℝ := sourceWindow s X
          let supports := fun i => FactoredDivisorWeights.support (sm i) (sn i)
          let weights := fun i =>
            FactoredDivisorWeights.coefficient (sm i) (sn i) (am i) (an i)
          (family.card : ℝ) ≤ X ^ (c / 2) →
          (∀ i ∈ family,
            1 ≤ M i ∧ 1 ≤ N i ∧
            X ^ α ≤ ((M i * N i : ℕ) : ℝ) ∧
            ((M i * N i : ℕ) : ℝ) ≤ X ^ (1 - ell - slack) ∧
            X ^ nu ≤ (N i : ℝ) ∧
            ((N i : ℝ) ≤ X ^ (8 / 35 : ℝ) ∨
              X ^ (27 / 35 : ℝ) ≤ ((M i * N i : ℕ) : ℝ)) ∧
            (∀ n ∈ sm i, M i < n ∧ n ≤ 2 * M i) ∧
            (∀ n ∈ sn i, N i < n ∧ n ≤ 2 * N i) ∧
            (∀ n ∈ sm i, |am i n| ≤ X ^ (c / 2)) ∧
            (∀ n ∈ sn i, |an i n| ≤ X ^ (c / 2))) →
          (1 / X) * (∫ x in Icc X (2 * X),
            HarmanDivisorWindow.remainder
              (FiniteDivisorFamily.support family supports)
              (FiniteDivisorFamily.coefficient family supports weights)
              (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  obtain ⟨c, hc, hfamily⟩ := FactoredDivisorVariableWindow.eventually_bound
    (ι := ι) α ell slack nu (s / 2)
    hα hell hslack hnu (by positivity) (by linarith)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hfamily, eventual_source_window_guards s hs hsmall]
    with X hf hw
  refine ⟨hf.1, ?_⟩
  intro family M N sm sn am an
  exact hf.2 (sourceWindow s X) family M N sm sn am an hw.2.1 hw.2.2

end FactoredDivisorVariableWindow

#print axioms FactoredDivisorVariableWindow.eventually_source_bound
run_cmd do
  for target in [``FactoredDivisorVariableWindow.eventual_source_window_guards,
      ``FactoredDivisorVariableWindow.eventually_source_region,
      ``FactoredDivisorVariableWindow.eventually_source_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FACTORED DIVISOR SOURCE WINDOW PASSED"
