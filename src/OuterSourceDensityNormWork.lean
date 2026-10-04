import OuterSourceCubeIntegralWork
import OuterKernelTwoSidedWork

/-! Logarithmic total variation of the nine-dimensional source separator,
uniformly in the truncation height and independent of representations. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterSourceDensityNormWork
open OuterSourceCubeIntegralWork OuterKernelTwoSidedWork OuterKernelIntegrableWork
open OuterBoxFourierKernelWork OuterRampLengthWork OuterSourceFourierWork
open OuterSmoothErrorSupportWork

def coordinateBudget (X s : ℝ) (i j : ℕ) (n : Fin 9) : ℝ :=
  (2*Real.pi)⁻¹*(2*cutoffLength X s i j n+4*Real.log ((width X)⁻¹)+4)
def coordinateConstant (s : ℝ) (i j : ℕ) (n : Fin 9) : ℝ :=
  2*slopeMass s i j n+4*Real.log 4+10

theorem coordinate_norm_bound (X s T : ℝ) (hX : 2 ≤ X) (i j : ℕ) (n : Fin 9) :
    (∫t in Ioc (-T) T, ‖((2*Real.pi)⁻¹:ℝ)*
      smoothedKernel 0 (cutoffLength X s i j n) (width X) t‖) ≤ coordinateBudget X s i j n := by
  have hw : 0 < width X := by unfold width; positivity
  have hw1 : width X ≤ 1 := by unfold width; apply (div_le_one (by positivity)).mpr; linarith
  have hc : 0 < (2*Real.pi)⁻¹ := by positivity
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc]
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ hc.le
  have he := setIntegral_le_integral (s := Ioc (-T) T)
    (kernel_integrable 0 (cutoffLength X s i j n) (width X) hw).norm
    (Filter.Eventually.of_forall (fun t => norm_nonneg _))
  apply he.trans
  simpa only [sub_zero,abs_of_pos (cutoffLength_pos X s hX i j n)] using
    kernel_whole_norm 0 (cutoffLength X s i j n) (width X) hw hw1

theorem density_norm_bound (X s T : ℝ) (hX : 2 ≤ X) (i j : ℕ) :
    (∫ω, ‖density X s i j ω‖ ∂frequencyCube T) ≤ ∏n : Fin 9,coordinateBudget X s i j n := by
  simp only [density,norm_prod,frequencyCube]
  rw [integral_fintype_prod_eq_prod (fun (n : Fin 9) (t : ℝ) =>
    ‖((2*Real.pi)⁻¹:ℝ)*smoothedKernel 0 (cutoffLength X s i j n) (width X) t‖)]
  exact Finset.prod_le_prod₀ (fun n _ => integral_nonneg (fun _ => norm_nonneg _))
    (fun n _ => coordinate_norm_bound X s T hX i j n)

theorem coordinateConstant_nonneg (s : ℝ) (i j : ℕ) (n : Fin 9) :
    0 ≤ coordinateConstant s i j n := by
  have hs := slopeMass_nonneg s i j n
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold coordinateConstant
  positivity

theorem coordinateBudget_log_bound (X s : ℝ) (hX : 2 ≤ X) (i j : ℕ) (n : Fin 9) :
    coordinateBudget X s i j n ≤ coordinateConstant s i j n*(1+Real.log X) := by
  have hx : 0 < X := by linarith
  have hl : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hs := slopeMass_nonneg s i j n
  have hp : (2*Real.pi)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by linarith [Real.pi_gt_three])
  have he : Real.log ((width X)⁻¹) = Real.log 4+Real.log X := by
    simp only [width,one_div,inv_inv]
    exact Real.log_mul (by norm_num) hx.ne'
  unfold coordinateBudget
  rw [he]
  calc
    _ ≤ 1*(2*cutoffLength X s i j n+4*(Real.log 4+Real.log X)+4) :=
      mul_le_mul_of_nonneg_right hp (by unfold cutoffLength; positivity)
    _ ≤ coordinateConstant s i j n*(1+Real.log X) := by
      unfold cutoffLength coordinateConstant
      nlinarith [mul_nonneg hs hl,mul_nonneg hl4 hl]

theorem density_norm_log_bound (X s T : ℝ) (hX : 2 ≤ X) (i j : ℕ) :
    (∫ω, ‖density X s i j ω‖ ∂frequencyCube T) ≤
      (∏n : Fin 9,coordinateConstant s i j n)*(1+Real.log X)^9 := by
  apply (density_norm_bound X s T hX i j).trans
  have hn (n : Fin 9) : 0 ≤ coordinateBudget X s i j n := by
    exact (integral_nonneg (fun _ => norm_nonneg _)).trans
      (coordinate_norm_bound X s T hX i j n)
  calc
    _ ≤ ∏n : Fin 9,coordinateConstant s i j n*(1+Real.log X) :=
      Finset.prod_le_prod₀ (fun n _ => hn n) (fun n _ => coordinateBudget_log_bound X s hX i j n)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

run_cmd do
  for decl in [``coordinate_norm_bound, ``density_norm_bound, ``coordinateConstant_nonneg,
      ``coordinateBudget_log_bound, ``density_norm_log_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSourceDensityNormWork
