import Item1PrefixArithmeticReduction
import Item1ArithmeticLogBound

/-! Explicit numerical majorants for the arithmetic factors in the genuine
logarithmic-prefix reduction. Collision counts remain explicit factors. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace Item1PrefixNumericalReduction
open Item1FiniteAbelPhase Item1LongLogPhase Item1LogPhasePolynomialReduction
open Item1ProductPrefixMoment Item1DifferenceBoxMajorant Item1PrefixArithmeticReduction
open Item1LinearPhaseDistance Item1SignedDistance Item1ArithmeticLogBound

/-- A finite product of explicit capped logarithmic bounds; the coefficient
zero branch is retained, so no division-by-zero exclusion is required. -/
def numericalProduct (d r s A Bmax : ℕ) (α : Fin d → ℝ) : ℝ :=
  ∏ j : Fin d, arithmeticBound (r*A^(j.val+1)) (s*Bmax^(j.val+1))
    (α j/(2*Real.pi))

theorem numericalProduct_nonneg (d r s A Bmax : ℕ) (α : Fin d → ℝ) :
    0 ≤ numericalProduct d r s A Bmax α :=
  Finset.prod_nonneg (fun _j _ => arithmeticBound_nonneg _ _ _)

/-- Every one-dimensional arithmetic sum is replaced by its explicit
logarithmic majorant, including zero coefficients and degenerate coordinate boxes. -/
theorem arithmeticProduct_le_numericalProduct (d r s A Bmax : ℕ) (α : Fin d → ℝ) :
    arithmeticProduct d r s A Bmax α ≤ numericalProduct d r s A Bmax α := by
  unfold arithmeticProduct numericalProduct
  apply Finset.prod_le_prod₀
  · intro j _
    exact Finset.sum_nonneg (fun _δ _ => distanceBound_nonneg _ _)
  · intro j _
    have h := arithmeticSum_succ_le_bound (r*A^(j.val+1)) (s*Bmax^(j.val+1))
      (α j/(2*Real.pi))
    unfold arithmeticSum at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro δ _
    congr 1
    ring

/-- The original prefix and every Taylor-sum moment are bounded with
explicit numerical factors. No unevaluated arithmetic sum remains in the
moment bound; the two exact collision factors still require estimates. -/
theorem prefix_and_numerical_even_moments (B : Finset ℕ) (hBne : B.Nonempty)
    (d M K A Bmax r s : ℕ) (t : ℝ) (hM : 1 ≤ M) (hA : 1 ≤ A)
    (hB : ∀ b ∈ B, b ≤ Bmax) (hhalf : 2*(A*Bmax) ≤ M)
    (hr : 1 ≤ r) (hs : 1 ≤ s) :
    (‖«prefix» (atom M t) K‖ ≤
      (1/((A:ℝ)*(B.card:ℝ)))*(∑ n ∈ Finset.range K, ‖U B d A ((M:ℝ)+n) t‖)+
      (K:ℝ)*(2*|t| *((((A*Bmax:ℕ):ℝ))/M)^(d+1))+
      2*(A:ℝ)*(Bmax:ℝ)) ∧
    ∀ n : ℕ, ‖U B d A ((M:ℝ)+n) t‖^(2*r*s) ≤
      (B.card:ℝ)^(2*r*s-2*s) * (A:ℝ)^(2*r*s-2*r) * J d r A *
      secondCollisionCount d s (fun b : B => (b.val:ℤ)) *
      numericalProduct d r s A Bmax
        (fun j : Fin d => phaseCoefficient ((M:ℝ)+n) t j.val) := by
  obtain ⟨hprefix, hmoment⟩ := prefix_and_factored_arithmetic_even_moments
    B hBne d M K A Bmax r s t hM hA hB hhalf hr hs
  refine ⟨hprefix, ?_⟩
  intro n
  have hmajor := arithmeticProduct_le_numericalProduct d r s A Bmax
    (fun j : Fin d => phaseCoefficient ((M:ℝ)+n) t j.val)
  have hJ : 0 ≤ J d r A := by unfold J; positivity
  have hJB : 0 ≤ secondCollisionCount d s (fun b : B => (b.val:ℤ)) := by
    unfold secondCollisionCount
    positivity
  exact (hmoment n).trans (mul_le_mul_of_nonneg_left hmajor
    (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hJ) hJB))

end Item1PrefixNumericalReduction

run_cmd do
  for target in [``Item1PrefixNumericalReduction.numericalProduct_nonneg,
      ``Item1PrefixNumericalReduction.arithmeticProduct_le_numericalProduct,
      ``Item1PrefixNumericalReduction.prefix_and_numerical_even_moments] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PREFIX NUMERICAL REDUCTION: 3 standard-axiom theorem guards passed."
