import SourceLiteralMoments

/-! v7. Actual reciprocal masses and amplitude bounds.
Uses the v6 elementary Mertens argument, not a PNT premise.
The source supports and prime-power coefficients are unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SourceLiteralMass
open SourceLiteralMoments SourceMassDischarge SourceMomentFinite
open PositiveInteriorCells PositiveInteriorModel Erdos374.HarmanGram152

def reciprocalMass (X : ℝ) (j : ℕ × ℕ) (i : Fin 3) : ℝ :=
  ∑ n ∈ support X j i, ArithmeticFunction.vonMangoldt n / (n : ℝ)

theorem support_pos (X : ℝ) (j : ℕ × ℕ) (i : Fin 3) (n : ℕ)
    (hn : n ∈ support X j i) : 0 < n := by
  fin_cases i
  · exact (by positivity : 0 < (2:ℕ)^j.1).trans_le (Finset.mem_Ico.mp hn).1
  · exact (by positivity : 0 < (2:ℕ)^j.2).trans_le (Finset.mem_Ico.mp hn).1
  · have h := (Finset.mem_Ioc.mp hn).1
    omega

theorem mass_nonneg (X : ℝ) (j : ℕ × ℕ) (i : Fin 3) :
    0 ≤ reciprocalMass X j i :=
  Finset.sum_nonneg (fun _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Nat.cast_nonneg _))

theorem mass_le_fifteen (X : ℝ) (j : ℕ × ℕ) (i : Fin 3)
    (hX : 2 ≤ X) (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X)) :
    reciprocalMass X j i ≤ 15 := by
  obtain ⟨hD, _, _, hsub⟩ := support_embedded X j (by linarith) hlog hj i
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Nat.cast_nonneg n))).trans
  exact full_interval_mass_le_fifteen (base X j i) hD

theorem factor_norm_le_mass (X : ℝ) (j : ℕ × ℕ) (i : Fin 3) (t : ℝ) :
    ‖factor X j i t‖ ≤ reciprocalMass X j i := by
  unfold factor
  rw [verticalDirichlet_eq_exponential152 _ _ 1 t
    (fun n hn => support_pos X j i n hn)]
  unfold Erdos374.HarmanAnalytic151MeanSquare.exponentialSum151
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  simp only [norm_mul, Erdos374.HarmanAnalytic151MeanSquare.norm_kernel151,
    mul_one, normalizedCoefficients152, Real.rpow_one, Complex.ofReal_natCast,
    norm_div, Complex.norm_natCast, mangoldt, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, le_refl]

theorem factor_norm_le_fifteen (X : ℝ) (j : ℕ × ℕ) (i : Fin 3) (t : ℝ)
    (hX : 2 ≤ X) (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X)) :
    ‖factor X j i t‖ ≤ 15 :=
  (factor_norm_le_mass X j i t).trans (mass_le_fifteen X j i hX hlog hj)

#print axioms factor_norm_le_fifteen
run_cmd do
  for n in [``support_pos, ``mass_nonneg, ``mass_le_fifteen,
      ``factor_norm_le_mass, ``factor_norm_le_fifteen] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V7 LITERAL MASS: VALID ONLY AFTER SUCCESSFUL COMPILATION"
end SourceLiteralMass
