import OuterBlockContourTailWork
import OuterContourSpatialWork

/-! Finite expansion and separator-frequency integrability of the
truncated continuous main contour. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterTruncatedContinuousWork
open OuterBlockContourTailWork OuterContourSpatialWork OuterBlockMainTermWork
open OuterBlockCofactorWork OuterActiveDyadicWork OuterRectangularBlocksWork
open OuterSourceCubeIntegralWork LongerTupleEncoding MellinWindowFactor MellinSmoothingFunction

def scalarKernel (X x δ ε σ : ℝ) (k : BlockKey) (n : ℕ) (t : ℝ) : ℂ :=
  (n:ℂ)^(-line σ t)*ContinuousCofactorMellin.cofactor (lower X k) (upper X k) (line σ t)*
    mellin (fun u => (Smooth1 smoothing ε u:ℂ)) (line σ t)*
    ((x:ℂ)^line σ t-((x-x*δ:ℝ):ℂ)^line σ t)

theorem scalar_integrable (X x δ ε σ : ℝ) (k : BlockKey) (n : ℕ)
    (hX : 0<X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2)) (hn : 0<n)
    (hε : ε∈Ioo 0 1) (hσ : 1<σ) (hσ2 : σ≤2) (hscale : 256*(scale k:ℝ)≤X) :
    Integrable (scalarKernel X x δ ε σ k n) := by
  have hlo := lower_pos X k hscale
  have hab := lower_le_upper X k hX
  have hxp : 0<x := hX.trans_le hx.1
  have hl : 0<x-x*δ := by nlinarith [hδ.2]
  have hh := ContinuousCofactorTail.short_kernel_integrable {n} (fun _ => 1)
    smoothing ε σ (x-x*δ) x (lower X k) (upper X k)
    hl hxp (by exact_mod_cast hlo) (by exact_mod_cast hab) (by simpa) hσ hσ2 hε
    differentiable nonnegative support mass_one
  unfold ContinuousCofactorTail.shortKernel at hh
  unfold scalarKernel
  simpa only [ContinuousCofactorTail.shortKernel,Erdos374.HarmanGram152.verticalDirichlet152,
    Finset.sum_singleton,one_mul,line] using hh

theorem truncated_sum (X s x δ ε σ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 1) (hσ : 1<σ) (hσ2 : σ≤2) (hscale : 256*(scale k:ℝ)≤X) :
    truncatedContinuous X s x δ ε σ i j k ω =
      ∑r∈blockSource X k,modeWeight X s i j ω r*
        (((1/(2*Real.pi):ℝ):ℂ)*∫t in Icc (-X) X,scalarKernel X x δ ε σ k (index r) t) := by
  have he (t : ℝ) : continuousKernel X s x δ ε σ i j k ω t =
      ∑r∈blockSource X k,modeWeight X s i j ω r*scalarKernel X x δ ε σ k (index r) t := by
    simp only [continuousKernel,modePolynomial,Finset.sum_mul,scalarKernel]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have hi (r : Representation) (hr : r∈blockSource X k) :
      IntegrableOn (scalarKernel X x δ ε σ k (index r)) (Icc (-X) X) :=
    (scalar_integrable X x δ ε σ k (index r) (by linarith) hx hδ
      ((scale_pos k).trans_le (index_range X hX k r hr).1) hε hσ hσ2 hscale).integrableOn
  unfold truncatedContinuous
  simp_rw [he]
  rw [integral_finsetSum _ (fun r hr => (hi r hr).const_mul _)]
  simp only [integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem density_truncated_integrable (X s x δ ε σ T : ℝ) (i j : ℕ) (k : BlockKey)
    (hX : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 1) (hσ : 1<σ) (hσ2 : σ≤2) (hscale : 256*(scale k:ℝ)≤X) :
    Integrable (fun ω => density X s i j ω*truncatedContinuous X s x δ ε σ i j k ω) (frequencyCube T) := by
  simp_rw [truncated_sum X s x δ ε σ i j k _ hX hx hδ hε hσ hσ2 hscale,Finset.mul_sum]
  apply integrable_finsetSum
  intro r hr
  have hh := (density_weights_integrable X s T i j (r,0)).mul_const
    (((1/(2*Real.pi):ℝ):ℂ)*∫t in Icc (-X) X,scalarKernel X x δ ε σ k (index r) t)
  simpa only [OuterCompletedCollectionWork.weights,mul_assoc] using hh

theorem density_full_integrable (X s x δ ε σ T : ℝ) (i j : ℕ) (k : BlockKey)
    (hX : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 (1/4)) (hσ : 1<σ) (hσ2 : σ≤2) (hscale : 256*(scale k:ℝ)≤X) :
    Integrable (fun ω => density X s i j ω*continuousContour X s x δ ε σ i j k ω) (frequencyCube T) := by
  have hh := (OuterMainCorrectionWork.density_correction_integrable X s x δ ε σ T
    i j k hX hx hδ hε hσ hσ2 hscale).add
    ((OuterMainCorrectionWork.density_mass_integrable X s T i j k).const_mul ((x*δ:ℝ):ℂ))
  convert hh using 1
  funext ω
  simp only [Pi.add_apply]
  ring

run_cmd do
  for decl in [``scalar_integrable, ``truncated_sum, ``density_truncated_integrable, ``density_full_integrable] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterTruncatedContinuousWork
