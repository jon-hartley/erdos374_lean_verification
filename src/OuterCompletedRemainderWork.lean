import OuterMainCorrectionWork

/-! Exact transfer from the literal localized remainder to the sharp
completed count minus its continuous contour main term. -/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterCompletedRemainderWork
open OuterMainCorrectionWork OuterBlockMainTermWork OuterBlockSharpCompletionWork
open OuterBlockIntegralWork OuterActiveDyadicWork OuterSourceCubeIntegralWork
open OuterLocalizedCoreWork OuterPairSourceDecompositionWork

def completedBox (X s x δ ε σ : ℝ) (i j : ℕ) : ℝ :=
  ∑k∈activeKeys X s i j, (∫ω, density X s i j ω *
    (completedCount X s (x-x*δ) x i j k ω-continuousContour X s x δ ε σ i j k ω)
      ∂frequencyCube (X^4)).re

def completedRemainder (X s x δ ε σ : ℝ) : ℝ :=
  ∑ij∈boxPairs s,completedBox X s x δ ε σ ij.1 ij.2

theorem density_block_integrable (X s L R T : ℝ) (i j : ℕ) (k : BlockKey) :
    Integrable (fun ω => density X s i j ω*blockModeSum X s L R i j k ω) (frequencyCube T) := by
  have he (ω : Fin 9→ℝ) : density X s i j ω*blockModeSum X s L R i j k ω =
      ∑r∈OuterRectangularBlocksWork.blockSource X k,
        ((OuterSmoothCoreWork.atomMultiplier X s i j r*
          UpperAfter545Remaining.floorKernel L R (LongerTupleEncoding.index r):ℝ):ℂ)*
        (density X s i j ω*OuterSeparatedFourierModeWork.sourceMode X s i j
          (OuterSourceReindexWork.drop r).1 r.1 (OuterSourceReindexWork.drop r).2.1
            (OuterSourceReindexWork.drop r).2.2 ω) := by
    simp only [blockModeSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  simp_rw [he]
  exact integrable_finsetSum _ (fun r _ => OuterTruncatedIntegralWork.weighted_mode_integrable X s L R T i j r)

theorem box_identity (X s x δ ε σ : ℝ) (i j : ℕ)
    (hX : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 (1/4)) (hσ : 1<σ) (hσ2 : σ≤2) :
    localizedBox X s (x-x*δ) x i j-completedBox X s x δ ε σ i j =
      (correctionBox X s x δ ε σ i j).re := by
  rw [localizedBox_eq_block_integrals]
  simp only [completedBox,correctionBox,Complex.re_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hi := density_correction_integrable X s x δ ε σ (X^4) i j k hX hx hδ hε hσ hσ2
    (OuterBlockCofactorScaleWork.active_lower X s hX hs hlog i j k hk).1
  have he (ω : Fin 9→ℝ) : density X s i j ω*
      (completedCount X s (x-x*δ) x i j k ω-continuousContour X s x δ ε σ i j k ω) =
      density X s i j ω*blockModeSum X s (x-x*δ) x i j k ω-
      density X s i j ω*(continuousContour X s x δ ε σ i j k ω-
        ((x*δ:ℝ):ℂ)*mainMass X s i j k ω) := by
    rw [blockModeSum_eq_completed X s x δ i j k ω hX hx hδ]
    ring
  simp_rw [he]
  rw [integral_sub (density_block_integrable X s (x-x*δ) x (X^4) i j k) hi,Complex.sub_re]
  ring

theorem full_identity (X s x δ ε σ : ℝ)
    (hX : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 (1/4)) (hσ : 1<σ) (hσ2 : σ≤2) :
    localizedRemainder X s (x-x*δ) x-completedRemainder X s x δ ε σ =
      (correction X s x δ ε σ).re := by
  simp only [localizedRemainder,completedRemainder,correction,Complex.re_sum,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun ij _ => box_identity X s x δ ε σ ij.1 ij.2 hX hs hlog hx hδ hε hσ hσ2)

theorem eventually_completed_error (s : ℝ) (hs : 0≤s) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 2≤X ∧ ∀ (x Y σ : ℝ), x∈Icc X (2*X) →
      0≤Y → Y≤X/2 → 1<σ → σ≤2 →
      |localizedRemainder X s (x-x*(Y/X)) x-
        completedRemainder X s x (Y/X) (X^(-19/20:ℝ)) σ|≤Y/(Real.log X)^A := by
  have hεlim : Tendsto (fun X : ℝ => X^(-19/20:ℝ)) atTop (nhds 0) := by
    simpa only [neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<19/20))
  filter_upwards [eventually_full_correction s hs A,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ)),
    hεlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))] with X hmain hlog hε
  refine ⟨hmain.1,?_⟩
  intro x Y σ hx hY hYX hσ hσ2
  have hXp : 0<X := by linarith [hmain.1]
  rw [full_identity X s x (Y/X) (X^(-19/20:ℝ)) σ hmain.1 hs hlog hx
    ⟨div_nonneg hY hXp.le,(div_le_iff₀ hXp).mpr (by linarith)⟩
    ⟨by positivity,hε⟩ hσ hσ2]
  exact (Complex.abs_re_le_norm _).trans (hmain.2 x Y σ hx hY hYX hσ hσ2)

run_cmd do
  for decl in [``density_block_integrable, ``box_identity, ``full_identity, ``eventually_completed_error] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterCompletedRemainderWork
