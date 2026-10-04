import SignedDivisorErrorDecomposition
import SmoothedWindowRegularity

/-!
All eight concrete errors are square integrable on the spatial interval.
The finite counting function is handled through its measurable floor
definition; the remaining terms are continuous compact transforms.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace SignedDivisorErrorRegularity
open SignedDivisorErrorDecomposition HarmanDivisorWindow HarmanDivisorContour
open Erdos374.HarmanGram152 SmoothedWindowTransfer

private theorem compact_memLp (f : ℝ → ℂ) (X : ℝ)
    (hf : ContinuousOn f (Icc X (2 * X))) :
    MemLp f 2 (volume.restrict (Icc X (2 * X))) := by
  apply (memLp_two_iff_integrable_sq_norm (hf.aestronglyMeasurable measurableSet_Icc)).mpr
  exact (hf.norm.pow 2).integrableOn_Icc

theorem errorTerms_integrable (s : Finset ℕ) (weight : ℕ → ℝ) (lo hi : ℕ)
    (ε X U H σ δ : ℝ) (hs : ∀ d ∈ s, 0 < d)
    (hlo : 0 < lo) (hhi : 0 < hi) (hX : 0 < X)
    (hε : ε ∈ Ioo 0 1) (hσ : 1 < σ) (hδ : δ ∈ Ico 0 1) :
    ∀ j : Fin 8, IntegrableOn
      (fun x => ‖errorTerms s weight lo hi ε X U H σ δ x j‖ ^ 2) (Icc X (2 * X)) := by
  let μ := volume.restrict (Icc X (2 * X))
  have hmain : MemLp (mainTerm s weight δ) 2 μ := by
    apply compact_memLp
    unfold mainTerm
    fun_prop
  have hsmooth : MemLp (smoothedMain s weight ε δ) 2 μ :=
    hmain.mul_const _
  have hremR : MemLp (fun x => remainder s weight (x - x * δ) x) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (SignedDivisorRegularity.measurable_remainder s weight δ).aestronglyMeasurable.restrict).mpr
    exact SignedDivisorRegularity.integrable_remainder_square s weight X δ hX.le
      ⟨hδ.1, hδ.2.le⟩
  have hcount : MemLp (fun x => (divisorCount s weight (x - x * δ) x : ℂ)) 2 μ := by
    have hremC : MemLp (fun x => (remainder s weight (x - x * δ) x : ℂ)) 2 μ :=
      hremR.ofReal
    have heq : (fun x => (divisorCount s weight (x - x * δ) x : ℂ)) =
        (fun x => (remainder s weight (x - x * δ) x : ℂ) + mainTerm s weight δ x) := by
      funext x
      unfold remainder mainTerm
      push_cast
      ring
    rw [heq]
    exact hremC.add hmain
  have hA := NormalizedMeanSquare.continuous_vertical s
    (fun d => (weight d : ℂ)) σ hs
  have hflat : Continuous (verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ) := by
    apply NormalizedMeanSquare.continuous_vertical
    intro n hn
    have hh := (Finset.mem_Ioc.mp hn).1
    omega
  have hcontinuous := FlatCofactorContour.continuous_polynomial lo hi σ hlo hhi hσ
  have hband (F : ℝ → ℂ) (a b : ℝ) (hF : Continuous F) :
      MemLp (transform F MellinSmoothingFunction.smoothing ε a b σ δ) 2 μ := by
    apply compact_memLp
    apply (SmoothedWindowRegularity.continuousOn_transform F
      MellinSmoothingFunction.smoothing ε a b σ δ hF hε (by linarith) hδ.2
      MellinSmoothingFunction.differentiable MellinSmoothingFunction.nonnegative
      MellinSmoothingFunction.support MellinSmoothingFunction.mass_one).mono
    intro x hx
    exact hX.trans_le hx.1
  have hD (a b : ℝ) : MemLp
      (productTransform s weight lo hi ε a b σ δ) 2 μ :=
    hband _ a b (hA.mul hflat)
  have hC : MemLp (continuousBand s weight lo hi ε (-H) H σ δ) 2 μ :=
    hband _ (-H) H (hA.mul hcontinuous)
  have he (j : Fin 8) : MemLp
      (fun x => errorTerms s weight lo hi ε X U H σ δ x j) 2 μ := by
    fin_cases j
    · exact hcount.sub ((hD (-X) X).const_mul normalization)
    · exact (hD (-X) (-U)).const_mul normalization
    · exact (hD (-U) (-H)).const_mul normalization
    · exact ((hD (-H) H).sub hC).const_mul normalization
    · exact (hC.const_mul normalization).sub hsmooth
    · exact hsmooth.sub hmain
    · exact (hD H U).const_mul normalization
    · exact (hD U X).const_mul normalization
  intro j
  exact (memLp_two_iff_integrable_sq_norm (he j).aestronglyMeasurable).mp (he j)

theorem mean_square_bound (s : Finset ℕ) (weight : ℕ → ℝ) (lo hi : ℕ)
    (ε X U H σ δ : ℝ) (B : Fin 8 → ℝ) (hs : ∀ d ∈ s, 0 < d)
    (hlo : 0 < lo) (hhi : 0 < hi) (hX : 0 < X)
    (hε : ε ∈ Ioo 0 1) (hσ : 1 < σ)
    (hδ : δ ∈ Ico 0 1) (hH : 0 ≤ H) (hHU : H ≤ U) (hUX : U ≤ X)
    (hbounds : ∀ j : Fin 8,
      (1 / X) * (∫ x in Icc X (2 * X),
        ‖errorTerms s weight lo hi ε X U H σ δ x j‖ ^ 2) ≤ B j) :
    (1 / X) * (∫ x in Icc X (2 * X),
      (remainder s weight (x - x * δ) x) ^ 2) ≤ 8 * ∑ j : Fin 8, B j :=
  SignedDivisorErrorDecomposition.mean_square_bound s weight lo hi ε X U H σ δ B
    hs hX hε (by linarith) hδ hH hHU hUX
    (errorTerms_integrable s weight lo hi ε X U H σ δ hs hlo hhi hX hε hσ hδ)
    hbounds

end SignedDivisorErrorRegularity

#print axioms SignedDivisorErrorRegularity.mean_square_bound
run_cmd do
  for target in [``SignedDivisorErrorRegularity.errorTerms_integrable,
      ``SignedDivisorErrorRegularity.mean_square_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "SIGNED DIVISOR ERROR REGULARITY PASSED"
