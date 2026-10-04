import OuterSourceCubeIntegralWork

/-! Exact frequency-integral representation of each full centered source
box. The density is independent of p,d,a,b and all signed coefficients and
floor-kernel main terms are retained. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace OuterTruncatedIntegralWork
open OuterSourceCubeIntegralWork OuterTruncatedCoreWork OuterNineCutTruncationWork
open OuterSmoothCoreWork OuterSmoothErrorSupportWork OuterSourceReindexWork
open OuterSeparatedFourierModeWork OuterSmoothStepWork OuterBufferedSourceWork
open LongerTupleEncoding UpperAfter545Remaining OuterPairSourceDecompositionWork

def centeredModeSum (X s L R : ℝ) (i j : ℕ) (ω : Fin 9 → ℝ) : ℂ :=
  ∑r∈ambient X, ((atomMultiplier X s i j r*floorKernel L R (index r):ℝ):ℂ)*
    sourceMode X s i j (drop r).1 r.1 (drop r).2.1 (drop r).2.2 ω

theorem weighted_mode_integrable (X s L R T : ℝ) (i j : ℕ) (r : Representation) :
    Integrable (fun ω => ((atomMultiplier X s i j r*floorKernel L R (index r):ℝ):ℂ)*
      (density X s i j ω*sourceMode X s i j (drop r).1 r.1 (drop r).2.1 (drop r).2.2 ω))
      (frequencyCube T) :=
  (mode_integrable X s T i j
    (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j))).const_mul _

theorem centered_mode_integrable (X s L R T : ℝ) (i j : ℕ) :
    Integrable (fun ω => density X s i j ω*centeredModeSum X s L R i j ω) (frequencyCube T) := by
  have he (ω : Fin 9 → ℝ) : density X s i j ω*centeredModeSum X s L R i j ω =
      ∑r∈ambient X, ((atomMultiplier X s i j r*floorKernel L R (index r):ℝ):ℂ)*
        (density X s i j ω*sourceMode X s i j (drop r).1 r.1 (drop r).2.1 (drop r).2.2 ω) := by
    simp only [centeredModeSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp_rw [he]
  exact integrable_finsetSum (ambient X) (fun r _ => weighted_mode_integrable X s L R T i j r)

theorem centered_integral_sum (X s L R T : ℝ) (hT : 0 ≤ T) (i j : ℕ) :
    (∫ω, density X s i j ω*centeredModeSum X s L R i j ω ∂frequencyCube T) =
      ∑r∈ambient X, ((atomMultiplier X s i j r*floorKernel L R (index r):ℝ):ℂ)*
        truncatedCuts X s T r i j := by
  have he (ω : Fin 9 → ℝ) : density X s i j ω*centeredModeSum X s L R i j ω =
      ∑r∈ambient X, ((atomMultiplier X s i j r*floorKernel L R (index r):ℝ):ℂ)*
        (density X s i j ω*sourceMode X s i j (drop r).1 r.1 (drop r).2.1 (drop r).2.2 ω) := by
    simp only [centeredModeSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp_rw [he]
  rw [integral_finsetSum (ambient X) (fun r _ => weighted_mode_integrable X s L R T i j r)]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_const_mul,source_cube_integral X s T hT r i j]

theorem truncatedBox_eq_integral (X s L R : ℝ) (i j : ℕ) :
    truncatedBox X s L R i j =
      (∫ω, density X s i j ω*centeredModeSum X s L R i j ω ∂frequencyCube (X^4)).re := by
  rw [centered_integral_sum X s L R (X^4) (by positivity) i j]
  simp only [truncatedBox,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem truncatedRemainder_eq_integrals (X s L R : ℝ) :
    truncatedRemainder X s L R = ∑ij∈boxPairs s,
      (∫ω, density X s ij.1 ij.2 ω*centeredModeSum X s L R ij.1 ij.2 ω
        ∂frequencyCube (X^4)).re := by
  simp only [truncatedRemainder,truncatedBox_eq_integral]

run_cmd do
  for decl in [``weighted_mode_integrable, ``centered_mode_integrable, ``centered_integral_sum,
      ``truncatedBox_eq_integral, ``truncatedRemainder_eq_integrals] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterTruncatedIntegralWork
