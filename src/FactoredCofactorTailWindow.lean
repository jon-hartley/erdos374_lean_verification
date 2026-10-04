import FactoredDivisorWeights
import HarmanCofactorTailWindow
import MellinCofactorCoverage

/-!
Middle-frequency bounds for the actual signed divisor contour when its
divisor coefficients are a full convolution of two real factor families.
The common cofactor scale is exactly A = M*N. Strict supports, both
coefficient energies, and the length guards at U remain explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace FactoredCofactorTailWindow
open Erdos374.HarmanGram152 SmoothedWindowTransfer

/-- The polynomial function inside the actual divisor product transform. -/
def polynomial (sm sn : Finset ℕ) (am an : ℕ → ℝ) (lo hi : ℕ)
    (σ t : ℝ) : ℂ :=
  verticalDirichlet152 (FactoredDivisorWeights.support sm sn)
    (fun d => (FactoredDivisorWeights.coefficient sm sn am an d : ℂ)) σ t *
      verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t

theorem polynomial_eq (sm sn : Finset ℕ) (am an : ℕ → ℝ) (lo hi : ℕ)
    (σ t : ℝ) :
    polynomial sm sn am an lo hi σ t =
      HarmanProductTailWindow.product lo hi sm sn am an σ t := by
  unfold polynomial HarmanProductTailWindow.product
  rw [FactoredDivisorWeights.vertical_product_support]
  ring

/-- The full twice-grouped polynomial retains all three-factor multiplicities. -/
theorem grouped_polynomial_eq (sm sn : Finset ℕ) (am an : ℕ → ℝ)
    (lo hi : ℕ) (σ t : ℝ) :
    verticalDirichlet152
      (HarmanDivisorWindow.productSupport (FactoredDivisorWeights.support sm sn)
        (Finset.Ioc lo hi))
      (fun d => (HarmanDivisorWindow.coefficient
        (FactoredDivisorWeights.support sm sn) (Finset.Ioc lo hi)
        (FactoredDivisorWeights.coefficient sm sn am an) d : ℂ)) σ t =
      HarmanProductTailWindow.product lo hi sm sn am an σ t := by
  rw [HarmanDivisorWindow.vertical_product_support]
  exact polynomial_eq sm sn am an lo hi σ t

theorem productTransform_eq (sm sn : Finset ℕ) (am an : ℕ → ℝ)
    (lo hi : ℕ) (ε a b σ δ x : ℝ) :
    HarmanDivisorContour.productTransform (FactoredDivisorWeights.support sm sn)
      (FactoredDivisorWeights.coefficient sm sn am an) lo hi ε a b σ δ x =
      transform (HarmanProductTailWindow.product lo hi sm sn am an σ)
        MellinSmoothingFunction.smoothing ε a b σ δ x := by
  unfold HarmanDivisorContour.productTransform
  have heq : (fun t =>
      verticalDirichlet152 (FactoredDivisorWeights.support sm sn)
        (fun d => (FactoredDivisorWeights.coefficient sm sn am an d : ℂ)) σ t *
        verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t) =
      HarmanProductTailWindow.product lo hi sm sn am an σ := by
    funext t
    exact polynomial_eq sm sn am an lo hi σ t
  rw [heq]

theorem eventually_bound (ell nu e ρ η : ℝ) (k : ℕ)
    (hell : 0 < ell) (hnu : 0 < nu) (he : 0 < e)
    (hρ : 0 < ρ) (hρell : ρ ≤ ell) (hρone : ρ < 1)
    (hη : 0 < η) (hηρ : η ≤ ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
        ∀ (lo hi M N : ℕ) (sm sn : Finset ℕ)
          (am an : ℕ → ℝ) (H U Y εs : ℝ),
          X ^ ell ≤ (lo : ℝ) → ((2 ^ k * lo : ℕ) : ℝ) ≤ X →
          hi ≤ 2 ^ k * lo →
          1 ≤ M → (M : ℝ) ≤ X → 1 ≤ N → (N : ℝ) ≤ X →
          X ^ nu ≤ (N : ℝ) →
          X ^ (e / 10) * U ^ (10 / 9 : ℝ) ≤ (lo * M * N : ℕ) →
          X ^ e * U ^ (6 / 7 : ℝ) ≤ max (lo * M : ℕ) (M * N : ℕ) →
          X ^ η ≤ H → H ≤ U → 2 * X ^ ρ ≤ U → U ≤ X →
          0 ≤ Y → Y < X → εs ∈ Ioo 0 1 →
          (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
          (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
          (∑ n ∈ sm, (am n) ^ 2) ≤ X ^ ε * M →
          (∑ n ∈ sn, (an n) ^ 2) ≤ X ^ ε * N →
          (1 / X) * (∫ x in Icc X (2 * X),
            ‖HarmanDivisorContour.productTransform
              (FactoredDivisorWeights.support sm sn)
              (FactoredDivisorWeights.coefficient sm sn am an) lo hi
              εs H U (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
                Y ^ 2 * X ^ (-c) ∧
          (1 / X) * (∫ x in Icc X (2 * X),
            ‖HarmanDivisorContour.productTransform
              (FactoredDivisorWeights.support sm sn)
              (FactoredDivisorWeights.coefficient sm sn am an) lo hi
              εs (-U) (-H) (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
                Y ^ 2 * X ^ (-c) := by
  obtain ⟨c, hc, ε, hε, hwindow⟩ := HarmanCofactorTailWindow.eventually_bound
    ell nu e ρ η k hell hnu he hρ hρell hρone hη hηρ
  refine ⟨c, hc, ε, hε, ?_⟩
  filter_upwards [hwindow] with X hh
  refine ⟨hh.1, ?_⟩
  intro lo hi M N sm sn am an H U Y εs hlo hcap hhi
    hM hMX hN hNX hNlow hproduct hpair hH hHU hUlow hUX
    hY hYX hεs hsm hsn hem hen
  have hbound := hh.2 lo hi M N sm sn am an H U Y εs hlo hcap hhi
    hM hMX hN hNX hNlow hproduct hpair hH hHU hUlow hUX
    hY hYX hεs hsm hsn hem hen
  simpa only [productTransform_eq] using hbound

/-- Specialization to the same common endpoints with A exactly equal to M*N. -/
theorem eventually_common_bound (ell nu e ρ η : ℝ) (k : ℕ)
    (hell : 0 < ell) (hnu : 0 < nu) (he : 0 < e)
    (hρ : 0 < ρ) (hρell : ρ ≤ ell) (hρone : ρ < 1)
    (hη : 0 < η) (hηρ : η ≤ ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
        ∀ (M N : ℕ) (sm sn : Finset ℕ) (am an : ℕ → ℝ) (H U Y εs : ℝ),
          let A : ℝ := (M * N : ℕ)
          let lo := MellinCofactorCoverage.lowerCutoff X A
          let hi := MellinCofactorCoverage.upperCutoff X A
          X ^ ell ≤ (lo : ℝ) → ((2 ^ k * lo : ℕ) : ℝ) ≤ X →
          hi ≤ 2 ^ k * lo →
          1 ≤ M → (M : ℝ) ≤ X → 1 ≤ N → (N : ℝ) ≤ X →
          X ^ nu ≤ (N : ℝ) →
          X ^ (e / 10) * U ^ (10 / 9 : ℝ) ≤ (lo * M * N : ℕ) →
          X ^ e * U ^ (6 / 7 : ℝ) ≤ max (lo * M : ℕ) (M * N : ℕ) →
          X ^ η ≤ H → H ≤ U → 2 * X ^ ρ ≤ U → U ≤ X →
          0 ≤ Y → Y < X → εs ∈ Ioo 0 1 →
          (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
          (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
          (∑ n ∈ sm, (am n) ^ 2) ≤ X ^ ε * M →
          (∑ n ∈ sn, (an n) ^ 2) ≤ X ^ ε * N →
          (1 / X) * (∫ x in Icc X (2 * X),
            ‖HarmanDivisorContour.productTransform
              (FactoredDivisorWeights.support sm sn)
              (FactoredDivisorWeights.coefficient sm sn am an) lo hi
              εs H U (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
                Y ^ 2 * X ^ (-c) ∧
          (1 / X) * (∫ x in Icc X (2 * X),
            ‖HarmanDivisorContour.productTransform
              (FactoredDivisorWeights.support sm sn)
              (FactoredDivisorWeights.coefficient sm sn am an) lo hi
              εs (-U) (-H) (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
                Y ^ 2 * X ^ (-c) := by
  obtain ⟨c, hc, ε, hε, hwindow⟩ := eventually_bound
    ell nu e ρ η k hell hnu he hρ hρell hρone hη hηρ
  refine ⟨c, hc, ε, hε, ?_⟩
  filter_upwards [hwindow] with X hh
  refine ⟨hh.1, ?_⟩
  intro M N sm sn am an H U Y εs
  dsimp only
  exact hh.2 (MellinCofactorCoverage.lowerCutoff X ((M * N : ℕ) : ℝ))
    (MellinCofactorCoverage.upperCutoff X ((M * N : ℕ) : ℝ))
    M N sm sn am an H U Y εs

end FactoredCofactorTailWindow

#print axioms FactoredCofactorTailWindow.eventually_common_bound
run_cmd do
  for target in [``FactoredCofactorTailWindow.polynomial_eq,
      ``FactoredCofactorTailWindow.grouped_polynomial_eq,
      ``FactoredCofactorTailWindow.productTransform_eq,
      ``FactoredCofactorTailWindow.eventually_bound,
      ``FactoredCofactorTailWindow.eventually_common_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FACTORED COFACTOR TAIL WINDOW PASSED"
