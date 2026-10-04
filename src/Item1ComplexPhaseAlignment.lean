import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Explicit unit complex factors align each summand with the nonnegative
real axis. The power-sum identity includes exponent zero and empty sums. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Item1ComplexPhaseAlignment

/-- A unit complex factor which rotates a complex value onto its norm. -/
def aligningUnit (z : ℂ) : ℂ :=
  if z = 0 then 1 else conj z / (‖z‖ : ℂ)

theorem norm_aligningUnit (z : ℂ) : ‖aligningUnit z‖ = 1 := by
  by_cases hz : z = 0
  · simp [aligningUnit, hz]
  · rw [aligningUnit, if_neg hz, norm_div, Complex.norm_conj,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
    exact div_self (norm_ne_zero_iff.mpr hz)

theorem aligningUnit_mul (z : ℂ) : aligningUnit z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [aligningUnit, hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    rw [aligningUnit, if_neg hz]
    calc
      conj z / (‖z‖ : ℂ) * z = (z * conj z) / (‖z‖ : ℂ) := by ring
      _ = (‖z‖ : ℂ) ^ 2 / (‖z‖ : ℂ) := by rw [Complex.mul_conj']
      _ = (‖z‖ : ℂ) := by field_simp

/-- Aligning each natural power turns its finite sum into the sum of norms.
No positivity hypothesis on the exponent is needed. -/
theorem sum_norm_pow_eq_norm_aligned_sum {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) (r : ℕ) :
    (∑ b ∈ s, ‖z b‖ ^ r) =
      ‖∑ b ∈ s, aligningUnit ((z b) ^ r) * (z b) ^ r‖ := by
  have hsum : (∑ b ∈ s, aligningUnit ((z b) ^ r) * (z b) ^ r) =
      ((∑ b ∈ s, ‖z b‖ ^ r : ℝ) : ℂ) := by
    simp only [aligningUnit_mul, norm_pow, Complex.ofReal_sum]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs]
  exact (abs_of_nonneg (Finset.sum_nonneg (fun b _ => pow_nonneg (norm_nonneg (z b)) r))).symm

end Item1ComplexPhaseAlignment

run_cmd do
  for target in [``Item1ComplexPhaseAlignment.norm_aligningUnit,
      ``Item1ComplexPhaseAlignment.aligningUnit_mul,
      ``Item1ComplexPhaseAlignment.sum_norm_pow_eq_norm_aligned_sum] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "COMPLEX PHASE ALIGNMENT: 3 standard-axiom theorem guards passed."
