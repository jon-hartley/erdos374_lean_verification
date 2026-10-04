import HarmanDivisorContour
import FlatCofactorContour
import SmoothedFrequencySplit
import SignedDivisorRegularity

/-!
Eight explicitly defined errors for one actual signed divisor count.
The split retains the contour normalization, both frequency signs,
the discrete-to-continuous replacement and the smoothing multiplier.
This module is an exact accounting identity; each error still needs
its corresponding analytic bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace SignedDivisorErrorDecomposition
open HarmanDivisorWindow HarmanDivisorContour SmoothedWindowTransfer
open Erdos374.HarmanGram152

def normalization : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)

def continuousBand (s : Finset ℕ) (weight : ℕ → ℝ) (lo hi : ℕ)
    (ε a b σ δ x : ℝ) : ℂ :=
  transform (fun t => verticalDirichlet152 s (fun d => (weight d : ℂ)) σ t *
    FlatCofactorContour.continuousPolynomial lo hi σ t)
    MellinSmoothingFunction.smoothing ε a b σ δ x

def mainTerm (s : Finset ℕ) (weight : ℕ → ℝ) (δ x : ℝ) : ℂ :=
  ((x * δ * reciprocalMass s weight : ℝ) : ℂ)

def smoothedMain (s : Finset ℕ) (weight : ℕ → ℝ) (ε δ x : ℝ) : ℂ :=
  mainTerm s weight δ x *
    mellin (fun u => (Smooth1 MellinSmoothingFunction.smoothing ε u : ℂ)) 1

/-- In order: sharp cutoff, negative high, negative middle, cofactor
replacement, continuous truncation, smoothing, positive middle, positive high. -/
def errorTerms (s : Finset ℕ) (weight : ℕ → ℝ) (lo hi : ℕ)
    (ε X U H σ δ x : ℝ) : Fin 8 → ℂ :=
  let D := fun a b => productTransform s weight lo hi ε a b σ δ x
  let C := continuousBand s weight lo hi ε (-H) H σ δ x
  let main := mainTerm s weight δ x
  let smooth := smoothedMain s weight ε δ x
  ![error s weight lo hi ε (-X) X σ δ x,
    normalization * D (-X) (-U),
    normalization * D (-U) (-H),
    normalization * (D (-H) H - C),
    normalization * C - smooth,
    smooth - main,
    normalization * D H U,
    normalization * D U X]

theorem decomposition (s : Finset ℕ) (weight : ℕ → ℝ) (lo hi : ℕ)
    (ε X U H σ δ x : ℝ) (hs : ∀ d ∈ s, 0 < d)
    (hε : ε ∈ Ioo 0 1) (hσ : 0 < σ) (hx : 0 < x) (hδ : δ < 1)
    (hH : 0 ≤ H) (hHU : H ≤ U) (hUX : U ≤ X) :
    (remainder s weight (x - x * δ) x : ℂ) =
      ∑ j : Fin 8, errorTerms s weight lo hi ε X U H σ δ x j := by
  let F := fun t => verticalDirichlet152 s (fun d => (weight d : ℂ)) σ t *
    verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t
  have hF : Continuous F := by
    apply Continuous.mul (NormalizedMeanSquare.continuous_vertical _ _ _ hs)
    apply NormalizedMeanSquare.continuous_vertical
    intro n hn
    have hh := (Finset.mem_Ioc.mp hn).1
    omega
  have hsplit := SmoothedFrequencySplit.five_bands F ε X U H σ δ x
    hF hε hσ hx hδ hH hHU hUX
  change productTransform s weight lo hi ε (-X) X σ δ x = _ at hsplit
  simp only [errorTerms, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  unfold error remainder mainTerm normalization
  push_cast
  rw [hsplit]
  dsimp only [F, productTransform]
  ring

theorem square_bound (s : Finset ℕ) (weight : ℕ → ℝ) (lo hi : ℕ)
    (ε X U H σ δ x : ℝ) (hs : ∀ d ∈ s, 0 < d)
    (hε : ε ∈ Ioo 0 1) (hσ : 0 < σ) (hx : 0 < x) (hδ : δ < 1)
    (hH : 0 ≤ H) (hHU : H ≤ U) (hUX : U ≤ X) :
    (remainder s weight (x - x * δ) x) ^ 2 ≤
      8 * ∑ j : Fin 8, ‖errorTerms s weight lo hi ε X U H σ δ x j‖ ^ 2 := by
  have hh := Erdos374.ExponentialSum151.norm_sum_sq_le_card_energy
    (Finset.univ : Finset (Fin 8)) (errorTerms s weight lo hi ε X U H σ δ x)
  rw [← decomposition s weight lo hi ε X U H σ δ x hs hε hσ hx hδ hH hHU hUX] at hh
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] using hh

theorem mean_square_bound (s : Finset ℕ) (weight : ℕ → ℝ) (lo hi : ℕ)
    (ε X U H σ δ : ℝ) (B : Fin 8 → ℝ) (hs : ∀ d ∈ s, 0 < d)
    (hX : 0 < X) (hε : ε ∈ Ioo 0 1) (hσ : 0 < σ)
    (hδ : δ ∈ Ico 0 1) (hH : 0 ≤ H) (hHU : H ≤ U) (hUX : U ≤ X)
    (hints : ∀ j : Fin 8, IntegrableOn
      (fun x => ‖errorTerms s weight lo hi ε X U H σ δ x j‖ ^ 2) (Icc X (2 * X)))
    (hbounds : ∀ j : Fin 8,
      (1 / X) * (∫ x in Icc X (2 * X),
        ‖errorTerms s weight lo hi ε X U H σ δ x j‖ ^ 2) ≤ B j) :
    (1 / X) * (∫ x in Icc X (2 * X),
      (remainder s weight (x - x * δ) x) ^ 2) ≤ 8 * ∑ j : Fin 8, B j := by
  have hrem := SignedDivisorRegularity.integrable_remainder_square s weight X δ
    hX.le ⟨hδ.1, hδ.2.le⟩
  have hsum : IntegrableOn
      (fun x => ∑ j : Fin 8, ‖errorTerms s weight lo hi ε X U H σ δ x j‖ ^ 2)
      (Icc X (2 * X)) := integrable_finsetSum _ (fun j hj => hints j)
  calc
    _ ≤ (1 / X) * (∫ x in Icc X (2 * X),
        8 * ∑ j : Fin 8, ‖errorTerms s weight lo hi ε X U H σ δ x j‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_mono_ae hrem (hsum.const_mul 8)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact square_bound s weight lo hi ε X U H σ δ x hs hε hσ
        (hX.trans_le hx.1) hδ.2 hH hHU hUX
    _ = 8 * ∑ j : Fin 8, (1 / X) * (∫ x in Icc X (2 * X),
        ‖errorTerms s weight lo hi ε X U H σ δ x j‖ ^ 2) := by
      rw [integral_const_mul, integral_finsetSum _ (fun j hj => hints j),
        ← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j hj => hbounds j))
      (by norm_num)

end SignedDivisorErrorDecomposition

#print axioms SignedDivisorErrorDecomposition.mean_square_bound
run_cmd do
  for target in [``SignedDivisorErrorDecomposition.decomposition,
      ``SignedDivisorErrorDecomposition.square_bound,
      ``SignedDivisorErrorDecomposition.mean_square_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "SIGNED DIVISOR ERROR DECOMPOSITION PASSED"
