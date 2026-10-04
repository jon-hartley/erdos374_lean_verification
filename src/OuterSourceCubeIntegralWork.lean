import OuterTruncatedCoreWork
import OuterSeparatedFourierModeWork
import Mathlib.MeasureTheory.Integral.Pi

/-! Fubini assembly of the nine truncated source integrals. The frequency
measure and density are independent of the source representation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterSourceCubeIntegralWork
open OuterMaskFrequencyWork OuterBoxFourierKernelWork OuterBoxFourierTailWork
open OuterRampTruncationWork OuterRampLengthWork OuterNineCutTruncationWork
open OuterSmoothErrorSupportWork OuterSmoothStepWork OuterBufferedSourceWork
open OuterSourceReindexWork OuterSeparatedFourierModeWork LongerTupleEncoding

def frequencyCube (T : ℝ) : Measure (Fin 9 → ℝ) :=
  Measure.pi (fun _ : Fin 9 => volume.restrict (Ioc (-T) T))
def density (X s : ℝ) (i j : ℕ) (ω : Fin 9 → ℝ) : ℂ :=
  ∏n : Fin 9, ((2*Real.pi)⁻¹:ℝ)*smoothedKernel 0 (cutoffLength X s i j n) (width X) (ω n)
def coordinate (X s : ℝ) (i j : ℕ) (n : Fin 9) (z t : ℝ) : ℂ :=
  ((2*Real.pi)⁻¹:ℝ)*integrand (width X) (cutoffLength X s i j n) z t

theorem coordinate_integrable (X s T : ℝ) (i j : ℕ) (n : Fin 9) (z : ℝ) :
    IntegrableOn (coordinate X s i j n z) (Ioc (-T) T) := by
  have hc : Continuous (coordinate X s i j n z) := by
    apply Continuous.const_mul
    apply Continuous.mul _ (kernel_continuous 0 _ _)
    unfold phase
    fun_prop
  exact (hc.intervalIntegrable (-T) T).1

theorem density_mode_product (X s : ℝ) (i j : ℕ) (z ω : Fin 9 → ℝ) :
    density X s i j ω*(∏n : Fin 9, phase (ω n) (z n)) =
      ∏n : Fin 9,coordinate X s i j n (z n) (ω n) := by
  rw [density,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro n _
  unfold coordinate integrand
  ring

theorem mode_integrable (X s T : ℝ) (i j : ℕ) (z : Fin 9 → ℝ) :
    Integrable (fun ω => density X s i j ω*(∏n : Fin 9,phase (ω n) (z n))) (frequencyCube T) := by
  simp_rw [density_mode_product]
  exact Integrable.fintype_prod (fun n => coordinate_integrable X s T i j n (z n))

theorem coordinate_integral (X s T : ℝ) (hT : 0 ≤ T) (i j : ℕ) (n : Fin 9) (z : ℝ) :
    (∫t in Ioc (-T) T, coordinate X s i j n z t) =
      truncatedRamp (width X) (cutoffLength X s i j n) T z := by
  rw [← intervalIntegral.integral_of_le (by linarith)]
  unfold coordinate truncatedRamp
  rw [intervalIntegral.integral_const_mul]
  rfl

theorem cube_integral (X s T : ℝ) (hT : 0 ≤ T) (i j : ℕ) (z : Fin 9 → ℝ) :
    (∫ω, density X s i j ω*(∏n : Fin 9,phase (ω n) (z n)) ∂frequencyCube T) =
      ∏n : Fin 9,truncatedRamp (width X) (cutoffLength X s i j n) T (z n) := by
  simp_rw [density_mode_product]
  rw [frequencyCube,integral_fintype_prod_eq_prod]
  exact Finset.prod_congr rfl (fun n _ => coordinate_integral X s T hT i j n (z n))

theorem source_cube_integral (X s T : ℝ) (hT : 0 ≤ T) (r : Representation) (i j : ℕ) :
    (∫ω, density X s i j ω*sourceMode X s i j (drop r).1 r.1 (drop r).2.1 (drop r).2.2 ω
      ∂frequencyCube T) = truncatedCuts X s T r i j := by
  exact cube_integral X s T hT i j
    (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j))

run_cmd do
  for decl in [``coordinate_integrable, ``density_mode_product, ``mode_integrable,
      ``coordinate_integral, ``cube_integral, ``source_cube_integral] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSourceCubeIntegralWork
