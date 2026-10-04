import HarmanDivisorWindow
import ProductCoefficientCap
import SignedFiniteWindowApproximation

/-!
Approximate an actual signed divisor count by its finite product contour.
All quotient floors and convolution multiplicities are retained. This
identity and error bound do not extract the reciprocal-mass main term.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace HarmanDivisorContour
open Erdos374.HarmanGram152 HarmanDivisorWindow SmoothedWindowTransfer

def productTransform (s : Finset ℕ) (weight : ℕ → ℝ) (lo hi : ℕ)
    (ε a b σ δ x : ℝ) : ℂ :=
  transform (fun t =>
    verticalDirichlet152 s (fun d => (weight d : ℂ)) σ t *
      verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t)
    MellinSmoothingFunction.smoothing ε a b σ δ x

def error (s : Finset ℕ) (weight : ℕ → ℝ) (lo hi : ℕ)
    (ε a b σ δ x : ℝ) : ℂ :=
  (divisorCount s weight (x - x * δ) x : ℂ) -
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      productTransform s weight lo hi ε a b σ δ x

theorem error_eq (s : Finset ℕ) (weight : ℕ → ℝ) (lo hi : ℕ)
    (ε a b σ δ x : ℝ) (hs : ∀ d ∈ s, 0 < d)
    (hleft : 0 ≤ x - x * δ) (hwindow : x - x * δ ≤ x)
    (hlo : ∀ d ∈ s, lo ≤ ⌊(x - x * δ) / d⌋₊)
    (hhi : ∀ d ∈ s, ⌊x / d⌋₊ ≤ hi) :
    error s weight lo hi ε a b σ δ x =
      SignedFiniteWindowApproximation.error
        (productSupport s (Finset.Ioc lo hi))
        (coefficient s (Finset.Ioc lo hi) weight) ε a b σ δ x := by
  unfold error SignedFiniteWindowApproximation.error
  rw [divisorCount_eq_sharp s weight lo hi (x - x * δ) x
    hs hleft hwindow hlo hhi]
  congr 1
  unfold productTransform transform
  simp_rw [vertical_product_support]

theorem eventual_approximation : ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
    ∀ (s : Finset ℕ) (weight : ℕ → ℝ) (D lo hi : ℕ) (x δ : ℝ),
      1 ≤ D → 1 ≤ hi → ((D * hi : ℕ) : ℝ) ≤ X ^ (2 : ℕ) →
      (∀ d ∈ s, 0 < d ∧ d ≤ D) →
      (∀ d ∈ s, |weight d| ≤ X ^ (1 / 1600 : ℝ)) →
      x ∈ Icc X (2 * X) → δ ∈ Icc 0 (1 / 2) →
      (∀ d ∈ s, lo ≤ ⌊(x - x * δ) / d⌋₊) →
      (∀ d ∈ s, ⌊x / d⌋₊ ≤ hi) →
      ‖error s weight lo hi (X ^ (-19 / 20 : ℝ)) (-X) X
        (1 + 1 / Real.log X) δ x‖ ≤ 4 * X ^ (2 / 25 : ℝ) := by
  filter_upwards [SignedFiniteWindowApproximation.eventual_approximation,
    ProductCoefficientCap.eventually_bound (1 / 200 : ℝ) (by norm_num)]
    with X ha hc
  refine ⟨ha.1, ?_⟩
  intro s weight D lo hi x δ hD hhi hDX hs hw hx hδ hlo hupper
  have hXp : 0 < X := (Real.exp_pos 1).trans_le ha.1
  have hxp : 0 < x := hXp.trans_le hx.1
  have hleft : 0 ≤ x - x * δ := by
    have hh := mul_le_mul_of_nonneg_left hδ.2 hxp.le
    linarith
  have hwindow : x - x * δ ≤ x := by nlinarith [hδ.1]
  have hsupport : ∀ n ∈ productSupport s (Finset.Ioc lo hi),
      0 < n ∧ n ≤ D * hi := by
    intro n hn
    exact ⟨productSupport_positive s (Finset.Ioc lo hi)
      (fun d hd => (hs d hd).1)
      (fun k hk => by have hh := (Finset.mem_Ioc.mp hk).1; omega) n hn,
      productSupport_le s (Finset.Ioc lo hi) D hi
        (fun d hd => (hs d hd).2) (fun k hk => (Finset.mem_Ioc.mp hk).2) n hn⟩
  have hcoeff : ∀ n ∈ productSupport s (Finset.Ioc lo hi),
      |coefficient s (Finset.Ioc lo hi) weight n| ≤ X ^ (1 / 200 : ℝ) := by
    intro n hn
    have hnX : (n : ℝ) ≤ X ^ (2 : ℕ) :=
      (by exact_mod_cast (hsupport n hn).2 : (n : ℝ) ≤ (D * hi : ℕ)).trans hDX
    have hh := hc.2 s (Finset.Ioc lo hi)
      (fun d => (weight d : ℂ)) (fun _ => 1) n (hsupport n hn).1 hnX
      (by
        intro d hd
        simpa only [Complex.norm_real, Real.norm_eq_abs,
          show (1 / 200 : ℝ) / 8 = 1 / 1600 by norm_num] using hw d hd)
      (by
        intro k hk
        simpa using Real.one_le_rpow hc.1 (by norm_num : (0 : ℝ) ≤ (1 / 200) / 8))
    rw [← coefficient_cast] at hh
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hh
  rw [error_eq s weight lo hi _ _ _ _ _ _
    (fun d hd => (hs d hd).1) hleft hwindow hlo hupper]
  exact ha.2 (productSupport s (Finset.Ioc lo hi))
    (coefficient s (Finset.Ioc lo hi) weight) (D * hi) x δ
    (by nlinarith) hDX hsupport hcoeff hx hδ

/-- Centering is exact algebra; the contour main term is still to be proved. -/
theorem centered_error (s : Finset ℕ) (weight : ℕ → ℝ) (lo hi : ℕ)
    (ε a b σ δ x : ℝ) :
    (remainder s weight (x - x * δ) x : ℂ) -
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        productTransform s weight lo hi ε a b σ δ x -
          ((x * δ * reciprocalMass s weight : ℝ) : ℂ)) =
      error s weight lo hi ε a b σ δ x := by
  unfold remainder error
  push_cast
  ring

end HarmanDivisorContour

#print axioms HarmanDivisorContour.eventual_approximation
run_cmd do
  for target in [``HarmanDivisorContour.error_eq,
      ``HarmanDivisorContour.eventual_approximation,
      ``HarmanDivisorContour.centered_error] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "HARMAN DIVISOR CONTOUR PASSED"
