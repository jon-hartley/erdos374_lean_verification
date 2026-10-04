import Item1PowerSumBox
import Item1RectangularPhaseSum
import Item1LinearPhaseDistance
import Item1WeightedMomentExpansion
import Item1KernelCorrelation

/-! An explicit finite small-divisor majorant for the weighted box moment.
The complex weights disappear from the bound. Estimating the resulting
arithmetic sum uniformly is still required for logarithmic cancellation. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped ComplexConjugate

namespace Item1BoxMomentMajorant
open Item1PowerSumBox Item1RectangularPhaseSum Item1LinearPhaseDistance
open Item1WeightedMomentExpansion Item1KernelCorrelation
open Item1PolynomialTupleProduct Item1PolynomialMomentIdentity Item1TupleCollisionCounting

def pairBound {κ : Type*} (d r s A : ℕ) (α : Fin d → ℝ)
    (u : κ → ℤ) (p q : Fin s → κ) : ℝ :=
  ∏ j : Fin d, distanceBound (r*A^(j.val+1)+1)
    ((α j*(differenceFrequency d s u p q j : ℝ))/(2*Real.pi))

def momentMajorant {κ : Type*} [Fintype κ] (d r s A : ℕ)
    (α : Fin d → ℝ) (u : κ → ℤ) : ℝ :=
  ∑ p : Fin s → κ, ∑ q : Fin s → κ, pairBound d r s A α u p q

theorem pairBound_nonneg {κ : Type*} (d r s A : ℕ) (α : Fin d → ℝ)
    (u : κ → ℤ) (p q : Fin s → κ) : 0 ≤ pairBound d r s A α u p q := by
  exact Finset.prod_nonneg (fun j _ => distanceBound_nonneg _ _)

theorem momentMajorant_nonneg {κ : Type*} [Fintype κ]
    (d r s A : ℕ) (α : Fin d → ℝ) (u : κ → ℤ) :
    0 ≤ momentMajorant d r s A α u := by
  exact Finset.sum_nonneg (fun p _ =>
    Finset.sum_nonneg (fun q _ => pairBound_nonneg d r s A α u p q))

/-- Each tuple correlation factors into one-dimensional geometric sums. -/
theorem norm_kernel_box_correlation_le_pairBound {κ : Type*}
    (d r s A : ℕ) (α : Fin d → ℝ) (u : κ → ℤ) (p q : Fin s → κ) :
    ‖∑ c ∈ box d r A,
      (∏ l, kernel α u c (p l))*conj (∏ l, kernel α u c (q l))‖ ≤
        pairBound d r s A α u p q := by
  simp_rw [kernel_tuple_correlation]
  unfold box pairBound
  apply norm_rectangular_phase_sum_le
  intro j
  have hθ : 2*Real.pi*((α j*(differenceFrequency d s u p q j : ℝ))/(2*Real.pi)) =
      α j*(differenceFrequency d s u p q j : ℝ) := by field_simp [Real.pi_ne_zero]
  simpa only [hθ] using norm_sum_Icc_zero_le_distance_bound
    (r*A^(j.val+1)) ((α j*(differenceFrequency d s u p q j : ℝ))/(2*Real.pi))

/-- Unit-bounded weights can be removed at the cost of an explicit tuple-pair sum. -/
theorem kernel_box_moment_le_majorant {κ : Type*} [Fintype κ]
    (d r s A : ℕ) (α : Fin d → ℝ) (u : κ → ℤ) (ε : κ → ℂ)
    (hε : ∀ b, ‖ε b‖ ≤ 1) :
    (∑ c ∈ box d r A, ‖∑ b, ε b*kernel α u c b‖^(2*s)) ≤
      momentMajorant d r s A α u := by
  apply (weighted_moment_le_correlations (box d r A) s ε
    (fun b c => kernel α u c b) hε).trans
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro q _
  exact norm_kernel_box_correlation_le_pairBound d r s A α u p q

/-- The exact-image moment in the bilinear bound has the same explicit majorant. -/
theorem kernel_image_moment_le_majorant {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d r s A : ℕ) (α : Fin d → ℝ) (w : ι → ℤ) (u : κ → ℤ) (ε : κ → ℂ)
    (hw0 : ∀ i, 0 ≤ w i) (hwA : ∀ i, w i ≤ (A:ℤ))
    (hε : ∀ b, ‖ε b‖ ≤ 1) :
    (∑ c ∈ frequencyImage
      (tupleFrequency (r := r) (powerFrequency d w) : (Fin r → ι) → (Fin d → ℤ)),
      ‖∑ b, ε b*kernel α u c b‖^(2*s)) ≤ momentMajorant d r s A α u := by
  exact (kernel_moment_sum_le_box d r s A α w u ε hw0 hwA).trans
    (kernel_box_moment_le_majorant d r s A α u ε hε)

end Item1BoxMomentMajorant

run_cmd do
  for target in [``Item1BoxMomentMajorant.pairBound_nonneg,
      ``Item1BoxMomentMajorant.momentMajorant_nonneg,
      ``Item1BoxMomentMajorant.norm_kernel_box_correlation_le_pairBound,
      ``Item1BoxMomentMajorant.kernel_box_moment_le_majorant,
      ``Item1BoxMomentMajorant.kernel_image_moment_le_majorant] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "BOX MOMENT MAJORANT: 5 standard-axiom theorem guards passed."
