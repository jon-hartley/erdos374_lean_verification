import OuterAbsoluteContourTailWork
import OuterBlockMassBudgetWork
import ContinuousCofactorTail
import SpatialErrorBudget

/-! The literal block's continuous main contour may be truncated at X
with a constant absolute error, uniformly in every separator phase. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterBlockContourTailWork
open OuterBlockMainTermWork OuterBlockMassBudgetWork OuterBlockCofactorWork
open OuterActiveDyadicWork OuterRectangularBlocksWork LongerTupleEncoding
open MellinWindowFactor MellinSmoothingFunction OuterCenteredFlatWork

def continuousKernel (X s x δ ε σ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) (t : ℝ) : ℂ :=
  modePolynomial X s i j k ω σ t*ContinuousCofactorMellin.cofactor (lower X k) (upper X k) (line σ t)*
    mellin (fun u => (Smooth1 smoothing ε u:ℂ)) (line σ t)*
    ((x:ℂ)^line σ t-((x-x*δ:ℝ):ℂ)^line σ t)

def truncatedContinuous (X s x δ ε σ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*∫t in Icc (-X) X,continuousKernel X s x δ ε σ i j k ω t

theorem modePolynomial_norm (X s σ t : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : 2≤X) (hσ : 1≤σ) : ‖modePolynomial X s i j k ω σ t‖≤1 := by
  have hM : (0:ℝ)<scale k := by exact_mod_cast scale_pos k
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑_r∈blockSource X k,1/(scale k:ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrM : (scale k:ℝ)≤ index r := by exact_mod_cast (index_range X hX k r hr).1
      have hrp : 0< index r := (scale_pos k).trans_le (index_range X hX k r hr).1
      have hr1 : (1:ℝ)≤ index r := by exact_mod_cast hrp
      have hc : ‖(index r:ℂ)^(-line σ t)‖≤1/(scale k:ℝ) := by
        rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ)< index r)]
        have he : (-line σ t).re = -σ := by simp [line]
        rw [he]
        calc
          _ ≤ (index r:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
          _ = 1/(index r:ℝ) := by rw [Real.rpow_neg_one,one_div]
          _ ≤ _ := one_div_le_one_div_of_le hM hrM
      rw [norm_mul]
      exact (mul_le_mul (modeWeight_norm X s i j ω r) hc (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    _ = ((blockSource X k).card:ℝ)/(scale k:ℝ) := by simp [div_eq_mul_inv]
    _ ≤ 1 := (div_le_one hM).mpr (by exact_mod_cast block_card X hX k)

theorem kernel_integrable (X s x δ ε σ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 1) (hσ : 1<σ) (hσ2 : σ≤2) (hscale : 256*(scale k:ℝ)≤X) :
    Integrable (continuousKernel X s x δ ε σ i j k ω) := by
  have hlo := lower_pos X k hscale
  have hab := lower_le_upper X k (by linarith)
  have hxp : 0<x := by linarith [hx.1]
  have hl : 0<x-x*δ := by nlinarith [hδ.2]
  have hS : ∀n∈LongerTupleCollection.support (blockSource X k) index,0<n := by
    intro n hn
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hn
    exact (scale_pos k).trans_le (index_range X hX k r hr).1
  have hh := ContinuousCofactorTail.short_kernel_integrable
    (LongerTupleCollection.support (blockSource X k) index)
    (LongerTupleCollection.coefficient (blockSource X k) index (modeWeight X s i j ω))
    smoothing ε σ (x-x*δ) x (lower X k) (upper X k)
    hl hxp (by exact_mod_cast hlo) (by exact_mod_cast hab) hS hσ hσ2 hε
    differentiable nonnegative support mass_one
  unfold continuousKernel
  simp_rw [polynomial_collected]
  exact hh

theorem truncation_bound (X s x δ ε : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 1) (hscale : 256*(scale k:ℝ)≤X) :
    ‖continuousContour X s x δ ε (1+1/Real.log X) i j k ω-
      truncatedContinuous X s x δ ε (1+1/Real.log X) i j k ω‖≤256*Real.exp 1 := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hlog : 1≤Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hσ : 1<1+1/Real.log X := by
    have : 0<1/Real.log X := by positivity
    linarith
  have hσ2 : 1+1/Real.log X≤2 := by
    have := (div_le_one (by linarith : 0<Real.log X)).mpr hlog
    linarith
  have hlo := lower_pos X k hscale
  have hab := lower_le_upper X k hXp
  have hh := OuterAbsoluteContourTailWork.whole_bound
    (continuousKernel X s x δ ε (1+1/Real.log X) i j k ω) (64*X*Real.exp 1) X
    (kernel_integrable X s x δ ε (1+1/Real.log X) i j k ω hX2 hx hδ hε hσ hσ2 hscale)
    (by positivity) hXp (by
      intro t ht
      unfold continuousKernel
      rw [←continuousFlat_eq_integral (lower X k) (upper X k) (1+1/Real.log X) t hlo hab hσ]
      exact OuterAbsoluteContourTailWork.kernel_bound X x δ ε t (lower X k) (upper X k)
        (modePolynomial X s i j k ω (1+1/Real.log X)) hX hx hδ hε
        (by omega) (by omega) (hXp.trans_le ht) (modePolynomial_norm X s _ t i j k ω hX2 hσ.le))
  unfold continuousContour truncatedContinuous
  change ‖((1/(2*Real.pi):ℝ):ℂ)*(∫t,continuousKernel X s x δ ε (1+1/Real.log X) i j k ω t)-
    ((1/(2*Real.pi):ℝ):ℂ)*(∫t in Icc (-X) X,continuousKernel X s x δ ε (1+1/Real.log X) i j k ω t)‖≤_
  rw [←mul_sub]
  exact ((SpatialErrorBudget.normalized_norm_le _).trans hh).trans_eq (by field_simp; ring)

run_cmd do
  for decl in [``modePolynomial_norm, ``kernel_integrable, ``truncation_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBlockContourTailWork
