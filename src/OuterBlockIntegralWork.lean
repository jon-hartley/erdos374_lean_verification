import OuterRectangularBlocksWork
import OuterLocalizedCoreWork
import OuterTruncatedIntegralWork

/-! Fourier assembly inside the selected rectangular blocks. The existing
separator density is unchanged, while every mode retains block geometry. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace OuterBlockIntegralWork
open OuterRectangularBlocksWork OuterActiveDyadicWork OuterLocalizedCoreWork
open OuterTruncatedIntegralWork OuterSourceCubeIntegralWork OuterSmoothCoreWork
open OuterSourceReindexWork OuterSeparatedFourierModeWork OuterNineCutTruncationWork
open LongerTupleEncoding UpperAfter545Remaining

def blockModeSum (X s L R : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9 → ℝ) : ℂ :=
  ∑r∈blockSource X k, ((atomMultiplier X s i j r*floorKernel L R (index r):ℝ):ℂ)*
    sourceMode X s i j (drop r).1 r.1 (drop r).2.1 (drop r).2.2 ω

theorem block_integral_sum (X s L R T : ℝ) (hT : 0 ≤ T) (i j : ℕ) (k : BlockKey) :
    (∫ω, density X s i j ω*blockModeSum X s L R i j k ω ∂frequencyCube T) =
      ∑r∈blockSource X k, ((atomMultiplier X s i j r*floorKernel L R (index r):ℝ):ℂ)*
        truncatedCuts X s T r i j := by
  have he (ω : Fin 9 → ℝ) : density X s i j ω*blockModeSum X s L R i j k ω =
      ∑r∈blockSource X k, ((atomMultiplier X s i j r*floorKernel L R (index r):ℝ):ℂ)*
        (density X s i j ω*sourceMode X s i j (drop r).1 r.1 (drop r).2.1 (drop r).2.2 ω) := by
    simp only [blockModeSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp_rw [he]
  rw [integral_finsetSum (blockSource X k) (fun r _ => weighted_mode_integrable X s L R T i j r)]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_const_mul,source_cube_integral X s T hT r i j]

theorem localizedBox_eq_block_integrals (X s L R : ℝ) (i j : ℕ) :
    localizedBox X s L R i j = ∑k∈activeKeys X s i j,
      (∫ω, density X s i j ω*blockModeSum X s L R i j k ω ∂frequencyCube (X^4)).re := by
  rw [localizedBox,localized_sum_blocks]
  apply Finset.sum_congr rfl
  intro k _
  rw [block_integral_sum X s L R (X^4) (by positivity) i j k]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  apply Finset.sum_congr rfl
  intro r _
  ring

run_cmd do
  for decl in [``block_integral_sum, ``localizedBox_eq_block_integrals] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBlockIntegralWork
