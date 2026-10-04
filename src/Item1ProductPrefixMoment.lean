import Item1ProductShiftReduction
import Item1PolynomialBilinearMoment

/-! The original logarithmic prefix and its product-shift polynomial sums
share one explicit family of finite moment inequalities. The collision factor
and the remaining weighted moments are retained without an upper estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace Item1ProductPrefixMoment
open Item1FiniteAbelPhase Item1LongLogPhase Item1LogPhasePolynomialReduction
open Item1PolynomialMomentIdentity Item1TupleCollisionCounting
open Item1PolynomialTupleProduct Item1PolynomialBilinearMoment

/-- The genuine product-shift Taylor sum, with a=1,...,A and b in B. -/
def U (B : Finset ℕ) (d A : ℕ) (x t : ℝ) : ℂ :=
  ∑ a : Fin A, ∑ b ∈ B, polynomialPhase d x t (((a.val+1)*b:ℕ):ℝ)

/-- Integer power sums of ordered r-tuples from 1,...,A. -/
def productTupleFrequency (d r A : ℕ) : (Fin r → Fin A) → (Fin d → ℤ) :=
  tupleFrequency (powerFrequency d (fun a : Fin A => (a.val:ℤ)+1))

/-- The exact collision factor, independent of x, t, and the second family B. -/
def J (d r A : ℕ) : ℝ :=
  ∑ c ∈ frequencyImage (productTupleFrequency d r A),
    (fiberMultiplicity (productTupleFrequency d r A) c : ℝ)^2

/-- The remaining weighted moment on the exact tuple-frequency image. -/
def T (B : Finset ℕ) (d r s A : ℕ) (x t : ℝ) (ε : B → ℂ) : ℝ :=
  ∑ c ∈ frequencyImage (productTupleFrequency d r A),
    ‖∑ b : B, ε b * kernel (fun j : Fin d => phaseCoefficient x t j.val)
      (fun b : B => (b.val:ℤ)) c b‖^(2*s)

/-- Conversion between the subtype-indexed integer-product sum and U. -/
theorem taylor_sum_eq_U (B : Finset ℕ) (d A : ℕ) (x t : ℝ) :
    (∑ b : B, ∑ a : Fin A,
      polynomialPhase d x t ((((a.val:ℤ)+1)*(b.val:ℤ):ℤ):ℝ)) = U B d A x t := by
  unfold U
  rw [Finset.sum_comm]
  simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_coe_sort B
    (fun b : ℕ => polynomialPhase d x t (((a.val:ℝ)+1)*(b:ℝ)))

/-- Unit weights exist for every center x. Empty indexing sets are allowed
in this algebraic statement; r and s are positive moment orders. -/
theorem exists_product_moment_weights (B : Finset ℕ) (d r s A : ℕ)
    (hr : 1 ≤ r) (hs : 1 ≤ s) (x t : ℝ) :
    ∃ ε : B → ℂ, (∀ b, ‖ε b‖ = 1) ∧
      ‖U B d A x t‖^(2*r*s) ≤
        (B.card:ℝ)^(2*r*s-2*s) * (A:ℝ)^(2*r*s-2*r) *
        J d r A * T B d r s A x t ε := by
  classical
  have h := taylor_bilinear_even_moment_reduction (ι := Fin A) (κ := B)
    d r s hr hs x t (fun a : Fin A => (a.val:ℤ)+1) (fun b : B => (b.val:ℤ))
  dsimp only at h
  obtain ⟨ε, hε, hbound⟩ := h
  refine ⟨ε, hε, ?_⟩
  simpa only [taylor_sum_eq_U, Fintype.card_coe, Fintype.card_fin,
    J, T, productTupleFrequency] using hbound

/-- One family of unit weights supports every center M+n in the original
prefix estimate. The bound includes K=0 and degree zero, and asserts the
moment estimate for every n, rather than only those below K. -/
theorem prefix_and_product_even_moments (B : Finset ℕ) (hBne : B.Nonempty)
    (d M K A Bmax r s : ℕ) (t : ℝ) (hM : 1 ≤ M) (hA : 1 ≤ A)
    (hB : ∀ b ∈ B, b ≤ Bmax) (hhalf : 2*(A*Bmax) ≤ M)
    (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ∃ ε : ℕ → B → ℂ, (∀ n b, ‖ε n b‖ = 1) ∧
      (‖«prefix» (atom M t) K‖ ≤
        (1/((A:ℝ)*(B.card:ℝ)))*(∑ n ∈ Finset.range K, ‖U B d A ((M:ℝ)+n) t‖)+
        (K:ℝ)*(2*|t| *((((A*Bmax:ℕ):ℝ))/M)^(d+1))+
        2*(A:ℝ)*(Bmax:ℝ)) ∧
      ∀ n : ℕ, ‖U B d A ((M:ℝ)+n) t‖^(2*r*s) ≤
        (B.card:ℝ)^(2*r*s-2*s) * (A:ℝ)^(2*r*s-2*r) *
        J d r A * T B d r s A ((M:ℝ)+n) t (ε n) := by
  classical
  have hex : ∀ n : ℕ, ∃ ε : B → ℂ, (∀ b, ‖ε b‖ = 1) ∧
      ‖U B d A ((M:ℝ)+n) t‖^(2*r*s) ≤
        (B.card:ℝ)^(2*r*s-2*s) * (A:ℝ)^(2*r*s-2*r) *
        J d r A * T B d r s A ((M:ℝ)+n) t ε :=
    fun n => exists_product_moment_weights B d r s A hr hs ((M:ℝ)+n) t
  choose ε hε hmoment using hex
  refine ⟨ε, hε, ?_, hmoment⟩
  simpa only [U] using Item1ProductShiftReduction.prefix_le_product_polynomial_shifts
    B hBne d M K A Bmax t hM hA hB hhalf

end Item1ProductPrefixMoment

run_cmd do
  for target in [``Item1ProductPrefixMoment.taylor_sum_eq_U,
      ``Item1ProductPrefixMoment.exists_product_moment_weights,
      ``Item1ProductPrefixMoment.prefix_and_product_even_moments] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PRODUCT PREFIX MOMENT: 3 standard-axiom theorem guards passed."
