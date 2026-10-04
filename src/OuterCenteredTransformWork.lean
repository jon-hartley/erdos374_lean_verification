import OuterCenteredContourWork

/-! Identify each literal centered block with the normalized truncated
Mellin transform of its discrete-minus-continuous cofactor polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterCenteredTransformWork
open OuterSharpContourWork OuterBlockContourTailWork OuterBlockMainTermWork
open OuterBlockSharpCompletionWork OuterBlockCofactorWork OuterCompletedCollectionWork
open OuterActiveDyadicWork OuterCenteredFlatWork MellinWindowFactor MellinSmoothingFunction
open Erdos374.HarmanGram152 LongerTupleCollection

theorem completed_kernel_integrable (X s x δ ε σ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 1) (hσ : 1<σ) (hσ2 : σ≤2) :
    Integrable (fun t => completedPolynomial X s σ t i j k ω*
      mellin (fun u => (Smooth1 smoothing ε u:ℂ)) (line σ t)*
      ((x:ℂ)^line σ t-((x-x*δ:ℝ):ℂ)^line σ t)) := by
  have hxp : 0<x := by linarith [hx.1]
  have hl : 0<x-x*δ := by nlinarith [hδ.2]
  have hp : ∀n∈support (entries X k) product,0<n := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hr,hn⟩ := Finset.mem_product.mp ha
    exact Nat.mul_pos
      (OuterAmbientSizeWork.ambient_index_pos X hX a.1 (Finset.mem_filter.mp hr).1)
      (by have := (Finset.mem_Ioc.mp hn).1; omega)
  have hi (z : ℝ) (hz : 0<z) := SmoothedDirichletKernel.integrable_integrand
    (support (entries X k) product) (coefficient (entries X k) product (weights X s i j ω))
    smoothing ε z σ hz hp hσ hσ2 hε differentiable nonnegative MellinSmoothingFunction.support mass_one
  apply ((hi x hxp).sub (hi (x-x*δ) hl)).congr
  filter_upwards with t
  simp only [Pi.sub_apply,SmoothedDirichletKernel.integrand,collected_polynomial]
  ring

theorem block_transform (X s x δ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hscale : 256*(scale k:ℝ)≤X) :
    discreteContour X s x δ i j k ω-
        truncatedContinuous X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k ω =
      ((1/(2*Real.pi):ℝ):ℂ)*SmoothedWindowTransfer.transform
        (fun t => modePolynomial X s i j k ω (1+1/Real.log X) t*
          centeredFlat (lower X k) (upper X k) (1+1/Real.log X) t)
        smoothing (X^(-19/20:ℝ)) (-X) X (1+1/Real.log X) δ x := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hlog : 1≤Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hσ : 1<1+1/Real.log X := by
    have : 0<1/Real.log X := by positivity
    linarith
  have hσ2 : 1+1/Real.log X≤2 := by
    have := (div_le_one (by linarith : 0<Real.log X)).mpr hlog
    linarith
  have hε : X^(-19/20:ℝ)∈Ioo 0 1 := ⟨by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg ((Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hX) (by norm_num)⟩
  have hd := completed_kernel_integrable X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k ω hX2 hx hδ hε hσ hσ2
  have hc := kernel_integrable X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k ω hX2 hx hδ hε hσ hσ2 hscale
  unfold discreteContour truncatedContinuous SmoothedWindowTransfer.transform
  rw [←mul_sub,←integral_sub hd.integrableOn hc.integrableOn]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [polynomial_factorization]
  unfold continuousKernel centeredFlat
  rw [continuousFlat_eq_integral (lower X k) (upper X k) (1+1/Real.log X) t
    (lower_pos X k hscale) (lower_le_upper X k hXp) hσ]
  ring

run_cmd do
  for decl in [``completed_kernel_integrable, ``block_transform] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterCenteredTransformWork
