import SourceLiteralMoments
import Item1PrimeLowSpectrum

/-! UNCOMPILED. Reapply the retained supported-moment theorem to subsets.
This never asserts that deleting terms decreases a Dirichlet-polynomial norm.
The exponents are chosen before the subset family. The full three supports,
floors and inherited 64-fold envelopes are unchanged. No cap is used here.
The retained SourceMomentFinite/SourceLogMoment dependency chain must be built.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Item1SubsetSourceMoments
open SourceLiteralMoments SourceMassDischarge SourceSelectedOrders
open SourceFractionalGeometryStrong Item1PrimeLowSpectrum
open PositiveInteriorModel PositiveInteriorCells Erdos374.HarmanGram152

/-- Geometry chooses one set of orders valid for every subset of each support. -/
theorem actual_subset_moments (X : ℝ) (j : ℕ × ℕ) (hX : 2 ≤ X)
    (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X)) :
    ∃ β : Fin 3 → ℝ,
      (∀ i, 4 ≤ β i) ∧ (2001/2000:ℝ) ≤ 2/β 0+2/β 1+2/β 2 ∧
      ∀ S : Fin 3 → Finset ℕ, (∀ i, S i ⊆ support X j i) →
      ∀ i, (∫ t in Icc (-X^(562/625:ℝ)) (X^(562/625:ℝ)),
        ‖verticalDirichlet152 (S i) mangoldt 1 t‖^(β i)) ≤
          commonConstant*(1+Real.log X)^18 := by
  have hX1 : 1 < X := by linarith
  obtain ⟨h,β,hdata,hguard,hS⟩ := SourceSelectedOrders.choose
    ((j.1:ℝ)*mesh X) ((j.2:ℝ)*mesh X) (source_triangle X hX1 j hj)
  refine ⟨β,?_,hS,?_⟩
  · intro i
    have hh : (2:ℝ) ≤ h i := by exact_mod_cast (hdata i).1
    linarith [(hdata i).2.2.1]
  · intro S hsubsets i
    obtain ⟨hD,hDX,hDx,hsub⟩ := support_embedded X j hX1 hlog hj i
    have hl := physical_length_guard X (exponent X j i) (β i) (base X j i) (h i)
      hX hlog hD hDx (hdata i).1 (hdata i).2.1 (hdata i).2.2.1
      (hdata i).2.2.2 (hguard i)
    have hU1 : 1 ≤ X^(562/625:ℝ) := Real.one_le_rpow hX1.le (by norm_num)
    have hUX : X^(562/625:ℝ) ≤ X := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1.le
        (by norm_num : (562/625:ℝ) ≤ 1)
    have hhr : (2:ℝ) ≤ h i := by exact_mod_cast (hdata i).1
    have hm := supported_moment (base X j i) (h i) (S i) X
      (-X^(562/625:ℝ)) (2*X^(562/625:ℝ)) (β i) hD (hdata i).1 (hdata i).2.1
      hX hDX (by linarith) (by linarith) (hdata i).2.2.1
      (by linarith [(hdata i).2.2.2]) ((hsubsets i).trans hsub) hl
    simpa only [show -X^(562/625:ℝ)+2*X^(562/625:ℝ)=X^(562/625:ℝ) by ring]
      using hm

/-- Prime filters are instantiated, not postulated as a new moment family. -/
theorem actual_prime_moments (X : ℝ) (j : ℕ × ℕ) (hX : 2 ≤ X)
    (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X)) :
    ∃ β : Fin 3 → ℝ,
      (∀ i, 4 ≤ β i) ∧ (2001/2000:ℝ) ≤ 2/β 0+2/β 1+2/β 2 ∧
      ∀ i, (∫ t in Icc (-X^(562/625:ℝ)) (X^(562/625:ℝ)),
        ‖primeFactor X j i t‖^(β i)) ≤ commonConstant*(1+Real.log X)^18 := by
  obtain ⟨β,hβ,hS,hm⟩ := actual_subset_moments X j hX hlog hj
  refine ⟨β,hβ,hS,?_⟩
  intro i
  simpa only [primeFactor] using hm (primeSupport X j)
    (fun _ => Finset.filter_subset _ _) i

run_cmd do
  for target in [``actual_subset_moments, ``actual_prime_moments] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1SubsetSourceMoments: 2 original theorem guards passed."

end Item1SubsetSourceMoments
