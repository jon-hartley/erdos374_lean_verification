import Item1PolynomialTupleProduct

/-! Exact tuple correlations of polynomial kernels, expressed through
differences of integer power sums. No estimate of their frequency spacing. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped ComplexConjugate

namespace Item1KernelCorrelation
open Item1PhasePerturbation Item1PolynomialTupleProduct Item1PolynomialMomentIdentity

def differenceFrequency {κ : Type*} (d s : ℕ) (u : κ → ℤ)
    (p q : Fin s → κ) : Fin d → ℤ :=
  tupleFrequency (powerFrequency d u) p - tupleFrequency (powerFrequency d u) q

theorem conj_unitPhase (x : ℝ) : conj (unitPhase x) = unitPhase (-x) := by
  unfold unitPhase
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg,
    mul_neg, neg_mul]

theorem kernel_tuple_product {κ : Type*} (d s : ℕ) (α : Fin d → ℝ)
    (u : κ → ℤ) (p : Fin s → κ) (c : Fin d → ℤ) :
    (∏ l, kernel α u c (p l)) =
      unitPhase (∑ j, α j*(tupleFrequency (powerFrequency d u) p j : ℝ)*(c j:ℝ)) := by
  unfold kernel
  rw [← unitPhase_finset_sum]
  congr 1
  simp only [tupleFrequency, Finset.sum_apply, powerFrequency, Int.cast_sum, Int.cast_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Finset.sum_mul]

theorem kernel_tuple_correlation {κ : Type*} (d s : ℕ) (α : Fin d → ℝ)
    (u : κ → ℤ) (p q : Fin s → κ) (c : Fin d → ℤ) :
    (∏ l, kernel α u c (p l))*conj (∏ l, kernel α u c (q l)) =
      unitPhase (∑ j, (α j*(differenceFrequency d s u p q j : ℝ))*(c j:ℝ)) := by
  rw [kernel_tuple_product, kernel_tuple_product, conj_unitPhase, ← unitPhase_add]
  congr 1
  rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [differenceFrequency, Pi.sub_apply, Int.cast_sub]
  ring

end Item1KernelCorrelation

run_cmd do
  for target in [``Item1KernelCorrelation.conj_unitPhase,
      ``Item1KernelCorrelation.kernel_tuple_product,
      ``Item1KernelCorrelation.kernel_tuple_correlation] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "KERNEL CORRELATION: 3 standard-axiom theorem guards passed."
