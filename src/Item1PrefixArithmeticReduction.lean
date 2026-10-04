import Item1ProductPrefixMoment
import Item1BoxMomentMajorant
import Item1DifferenceBoxMajorant

/-! The actual logarithmic prefix is reduced to collision counts and an
explicit arithmetic majorant. The auxiliary unit weights and weighted
image moments are eliminated from the statements below. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace Item1PrefixArithmeticReduction
open Item1FiniteAbelPhase Item1LongLogPhase Item1LogPhasePolynomialReduction
open Item1ProductPrefixMoment Item1BoxMomentMajorant
open Item1DifferenceBoxMajorant

/-- At every real center, the genuine Taylor sum has a moment bound with
the explicit box majorant in place of the existential weighted moment. -/
theorem product_even_moment_le_arithmetic_majorant (B : Finset ℕ)
    (d r s A : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (x t : ℝ) :
    ‖U B d A x t‖^(2*r*s) ≤
      (B.card:ℝ)^(2*r*s-2*s) * (A:ℝ)^(2*r*s-2*r) * J d r A *
      momentMajorant d r s A (fun j : Fin d => phaseCoefficient x t j.val)
        (fun b : B => (b.val:ℤ)) := by
  classical
  obtain ⟨ε, hε, hmoment⟩ := exists_product_moment_weights B d r s A hr hs x t
  have hmajor := kernel_image_moment_le_majorant (ι := Fin A) (κ := B) d r s A
    (fun j : Fin d => phaseCoefficient x t j.val)
    (fun a : Fin A => (a.val:ℤ)+1) (fun b : B => (b.val:ℤ)) ε
    (by intro a; positivity)
    (by intro a; exact_mod_cast Nat.succ_le_of_lt a.isLt)
    (fun b => (hε b).le)
  have hT : T B d r s A x t ε ≤
      momentMajorant d r s A (fun j : Fin d => phaseCoefficient x t j.val)
        (fun b : B => (b.val:ℤ)) := by
    simpa only [T, productTupleFrequency] using hmajor
  have hJ : 0 ≤ J d r A := by unfold J; positivity
  exact hmoment.trans (mul_le_mul_of_nonneg_left hT
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hJ))

/-- The original prefix bound and all of its Taylor-sum moment bounds,
with no existential phase weights in the conclusion. No estimate on J or
on the explicit arithmetic majorant is asserted here. -/
theorem prefix_and_arithmetic_even_moments (B : Finset ℕ) (hBne : B.Nonempty)
    (d M K A Bmax r s : ℕ) (t : ℝ) (hM : 1 ≤ M) (hA : 1 ≤ A)
    (hB : ∀ b ∈ B, b ≤ Bmax) (hhalf : 2*(A*Bmax) ≤ M)
    (hr : 1 ≤ r) (hs : 1 ≤ s) :
    (‖«prefix» (atom M t) K‖ ≤
      (1/((A:ℝ)*(B.card:ℝ)))*(∑ n ∈ Finset.range K, ‖U B d A ((M:ℝ)+n) t‖)+
      (K:ℝ)*(2*|t| *((((A*Bmax:ℕ):ℝ))/M)^(d+1))+
      2*(A:ℝ)*(Bmax:ℝ)) ∧
    ∀ n : ℕ, ‖U B d A ((M:ℝ)+n) t‖^(2*r*s) ≤
      (B.card:ℝ)^(2*r*s-2*s) * (A:ℝ)^(2*r*s-2*r) * J d r A *
      momentMajorant d r s A
        (fun j : Fin d => phaseCoefficient ((M:ℝ)+n) t j.val)
        (fun b : B => (b.val:ℤ)) := by
  constructor
  · simpa only [U] using Item1ProductShiftReduction.prefix_le_product_polynomial_shifts
      B hBne d M K A Bmax t hM hA hB hhalf
  · intro n
    exact product_even_moment_le_arithmetic_majorant B d r s A hr hs ((M:ℝ)+n) t

/-- The explicit pair majorant is further bounded by the second exact
collision count and a product of one-dimensional arithmetic sums. -/
theorem prefix_and_factored_arithmetic_even_moments (B : Finset ℕ) (hBne : B.Nonempty)
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
      arithmeticProduct d r s A Bmax
        (fun j : Fin d => phaseCoefficient ((M:ℝ)+n) t j.val) := by
  obtain ⟨hprefix, hmoment⟩ := prefix_and_arithmetic_even_moments
    B hBne d M K A Bmax r s t hM hA hB hhalf hr hs
  refine ⟨hprefix, ?_⟩
  intro n
  have hmajor := momentMajorant_le_collision_arithmeticProduct d r s A Bmax
    (fun j : Fin d => phaseCoefficient ((M:ℝ)+n) t j.val)
    (fun b : B => (b.val:ℤ))
    (by intro b; positivity)
    (by intro b; exact_mod_cast hB b.val b.property)
  have hJ : 0 ≤ J d r A := by unfold J; positivity
  have hproduct := mul_le_mul_of_nonneg_left hmajor
    (mul_nonneg (mul_nonneg (by positivity : 0 ≤ (B.card:ℝ)^(2*r*s-2*s))
      (by positivity : 0 ≤ (A:ℝ)^(2*r*s-2*r))) hJ)
  exact (hmoment n).trans (by simpa only [mul_assoc] using hproduct)

end Item1PrefixArithmeticReduction

run_cmd do
  for target in [``Item1PrefixArithmeticReduction.product_even_moment_le_arithmetic_majorant,
      ``Item1PrefixArithmeticReduction.prefix_and_arithmetic_even_moments,
      ``Item1PrefixArithmeticReduction.prefix_and_factored_arithmetic_even_moments] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PREFIX ARITHMETIC REDUCTION: 3 standard-axiom theorem guards passed."
