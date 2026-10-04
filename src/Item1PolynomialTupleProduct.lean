import Item1PhasePerturbation
import Item1PolynomialMomentIdentity

/-! Exact collection of polynomial phases by ordered-tuple power sums.
All integer signs and degrees 1 through d are retained. These identities do
not assert cancellation or a bound on the number of frequency collisions. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace Item1PolynomialTupleProduct
open Item1PhasePerturbation Item1PolynomialMomentIdentity

/-- Polynomial phase on an integer product. Coefficients use angular units. -/
def bilinearPhase {ι β : Type*} {d : ℕ} (α : Fin d → ℝ)
    (w : ι → ℤ) (u : β → ℤ) (i : ι) (b : β) : ℂ :=
  unitPhase (∑ j : Fin d, α j * ((w i*u b:ℤ):ℝ)^(j.val+1))

/-- The same phase after collecting an ordered tuple into its power sums. -/
def kernel {β : Type*} {d : ℕ} (α : Fin d → ℝ) (u : β → ℤ)
    (c : Fin d → ℤ) (b : β) : ℂ :=
  unitPhase (∑ j : Fin d, α j * (u b:ℝ)^(j.val+1) * (c j:ℝ))

/-- Finite multiplication adds the real angular phases. -/
theorem unitPhase_finset_sum {κ : Type*} (s : Finset κ) (f : κ → ℝ) :
    unitPhase (∑ i ∈ s, f i) = ∏ i ∈ s, unitPhase (f i) := by
  simp only [unitPhase, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

/-- Each bilinear polynomial phase has unit norm. -/
theorem bilinearPhase_norm {ι β : Type*} {d : ℕ} (α : Fin d → ℝ)
    (w : ι → ℤ) (u : β → ℤ) (i : ι) (b : β) :
    ‖bilinearPhase α w u i b‖ = 1 := unitPhase_norm _

/-- Each collected polynomial phase has unit norm. -/
theorem kernel_norm {β : Type*} {d : ℕ} (α : Fin d → ℝ) (u : β → ℤ)
    (c : Fin d → ℤ) (b : β) : ‖kernel α u c b‖ = 1 := unitPhase_norm _

/-- A product over an ordered tuple depends only on its integer power sums.
This includes empty tuples and degree zero, without positivity assumptions. -/
theorem tuple_product_eq_kernel {ι β : Type*} {d r : ℕ} (α : Fin d → ℝ)
    (w : ι → ℤ) (u : β → ℤ) (p : Fin r → ι) (b : β) :
    (∏ l : Fin r, bilinearPhase α w u (p l) b) =
      kernel α u (tupleFrequency (powerFrequency d w) p) b := by
  unfold bilinearPhase kernel
  rw [← unitPhase_finset_sum]
  congr 1
  simp only [Int.cast_mul, mul_pow, tupleFrequency, Finset.sum_apply,
    powerFrequency, Int.cast_sum, Int.cast_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

end Item1PolynomialTupleProduct

run_cmd do
  for target in [``Item1PolynomialTupleProduct.unitPhase_finset_sum,
      ``Item1PolynomialTupleProduct.bilinearPhase_norm,
      ``Item1PolynomialTupleProduct.kernel_norm,
      ``Item1PolynomialTupleProduct.tuple_product_eq_kernel] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "POLYNOMIAL TUPLE PRODUCT: 4 standard-axiom theorem guards passed."
