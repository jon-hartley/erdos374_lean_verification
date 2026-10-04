import CompactIntegral

/-! Exact adjacent-interval splitting, with endpoint null sets handled. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace CompactIntegralSplit

theorem split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hf : IntegrableOn f (Icc a c)) :
    (∫ t in Icc a c, f t) = (∫ t in Icc a b, f t) + ∫ t in Icc b c, f t := by
  have hiab : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (hf.mono_set (Icc_subset_Icc_right hbc))
  have hibc : IntervalIntegrable f volume b c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hbc).mpr
      (hf.mono_set (Icc_subset_Icc_left hab))
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hab.trans hbc),
    ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hbc]
  exact (intervalIntegral.integral_add_adjacent_intervals hiab hibc).symm

end CompactIntegralSplit

#print axioms CompactIntegralSplit.split
run_cmd do
  let axioms ← Lean.collectAxioms ``CompactIntegralSplit.split
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "COMPACT INTEGRAL SPLIT PASSED"
