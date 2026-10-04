import OuterCenteredTransformWork

/-! Spatial integrability of the fully assembled centered contour. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterCenteredSpatialWork
open OuterCenteredContourWork OuterContourSpatialWork OuterTruncatedContinuousWork
open OuterBlockContourTailWork OuterBlockMainTermWork OuterBlockCofactorWork
open OuterActiveDyadicWork OuterRectangularBlocksWork OuterSourceCubeIntegralWork
open OuterSharpContourWork OuterSharpContourRegularityWork OuterSharpContourAssemblyWork
open OuterCompletedCollectionWork LongerTupleEncoding MellinWindowFactor MellinSmoothingFunction
open OuterCenteredFlatWork Erdos374.HarmanGram152

theorem truncated_integral_sum (X s x δ ε σ : ℝ) (i j : ℕ) (k : BlockKey)
    (hX : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 1) (hσ : 1<σ) (hσ2 : σ≤2) (hscale : 256*(scale k:ℝ)≤X) :
    (∫ω,density X s i j ω*truncatedContinuous X s x δ ε σ i j k ω ∂frequencyCube (X^4)) =
      ∑r∈blockSource X k,(∫ω,density X s i j ω*modeWeight X s i j ω r ∂frequencyCube (X^4))*
        (((1/(2*Real.pi):ℝ):ℂ)*∫t in Icc (-X) X,scalarKernel X x δ ε σ k (index r) t) := by
  simp_rw [truncated_sum X s x δ ε σ i j k _ hX hx hδ hε hσ hσ2 hscale,Finset.mul_sum]
  have he (ω : Fin 9→ℝ) (r : Representation) (C : ℂ) : density X s i j ω*(modeWeight X s i j ω r*C) =
      (density X s i j ω*modeWeight X s i j ω r)*C := (mul_assoc _ _ _).symm
  simp_rw [he]
  have hi (r : Representation) : Integrable (fun ω => density X s i j ω*modeWeight X s i j ω r) (frequencyCube (X^4)) := by
    simpa only [weights] using density_weights_integrable X s (X^4) i j (r,0)
  rw [integral_finsetSum _ (fun r _ => (hi r).mul_const _)]
  simp only [integral_mul_const]

theorem scalar_continuous (X δ ε σ : ℝ) (k : BlockKey) (n : ℕ)
    (hX : 0<X) (hn : 0<n) (hδ : δ<1) (hε : ε∈Ioo 0 1) (hσ : 1<σ)
    (hscale : 256*(scale k:ℝ)≤X) :
    ContinuousOn (fun x => ((1/(2*Real.pi):ℝ):ℂ)*∫t in Icc (-X) X,
      scalarKernel X x δ ε σ k n t) (Ioi (0:ℝ)) := by
  have hlo := lower_pos X k hscale
  have hab := lower_le_upper X k hX
  let F := fun t => verticalDirichlet152 {n} (fun _ => 1) σ t*continuousFlat (lower X k) (upper X k) σ t
  have hF : Continuous F := (NormalizedMeanSquare.continuous_vertical _ _ _ (by simpa)).mul
    (FlatCofactorContour.continuous_polynomial _ _ σ (by omega) (by omega) hσ)
  have hh := (SmoothedWindowRegularity.continuousOn_transform F smoothing ε (-X) X σ δ hF hε
    (by linarith) hδ differentiable nonnegative support mass_one).const_mul ((1/(2*Real.pi):ℝ):ℂ)
  apply hh.congr
  intro x hx
  dsimp only
  unfold SmoothedWindowTransfer.transform
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [F,verticalDirichlet152,Finset.sum_singleton,one_mul,scalarKernel]
  rw [continuousFlat_eq_integral _ _ σ t hlo hab hσ]
  rfl

theorem centered_continuous (X s δ : ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hδ : δ∈Icc 0 (1/2)) (hε : X^(-19/20:ℝ)∈Ioo 0 (1/4)) :
    ContinuousOn (fun x => centeredRemainder X s x δ) (Icc X (2*X)) := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hσ : 1<1+1/Real.log X := by
    have : 0<1/Real.log X := by positivity
    linarith
  have hσ2 : 1+1/Real.log X≤2 := by
    have := (div_le_one (by linarith : 0<Real.log X)).mpr (show 1≤Real.log X by linarith)
    linarith
  have hε1 : X^(-19/20:ℝ)∈Ioo 0 1 := ⟨hε.1,by linarith [hε.2]⟩
  have hi (i j : ℕ) (k : BlockKey) (hk : k∈activeKeys X s i j) :
      ContinuousOn (fun x => ∫ω,density X s i j ω*(discreteContour X s x δ i j k ω-
        truncatedContinuous X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k ω) ∂frequencyCube (X^4))
        (Icc X (2*X)) := by
    have hscale := (OuterBlockCofactorScaleWork.active_lower X s hX2 hs hlog i j k hk).1
    have hd : ContinuousOn (fun x => ∑a∈entries X k,
        (∫ω,density X s i j ω*weights X s i j ω a ∂frequencyCube (X^4))*
        (((1/(2*Real.pi):ℝ):ℂ)*∫t in Icc (-X) X,
          singleKernel x δ (X^(-19/20:ℝ)) (1+1/Real.log X) (product a) t)) (Icc X (2*X)) := by
      apply continuousOn_finsetSum
      intro a ha
      obtain ⟨hr,hn⟩ := Finset.mem_product.mp ha
      have hp : 0<product a := Nat.mul_pos
        (OuterAmbientSizeWork.ambient_index_pos X hX2 a.1 (Finset.mem_filter.mp hr).1)
        (by have := (Finset.mem_Ioc.mp hn).1; omega)
      exact ((single_continuous X δ (product a) hp hX (by linarith [hδ.2])).const_mul _).mono
        (fun x hx => hXp.trans_le hx.1)
    have ht : ContinuousOn (fun x => ∑r∈blockSource X k,
        (∫ω,density X s i j ω*modeWeight X s i j ω r ∂frequencyCube (X^4))*
        (((1/(2*Real.pi):ℝ):ℂ)*∫t in Icc (-X) X,
          scalarKernel X x δ (X^(-19/20:ℝ)) (1+1/Real.log X) k (index r) t)) (Icc X (2*X)) := by
      apply continuousOn_finsetSum
      intro r hr
      exact ((scalar_continuous X δ (X^(-19/20:ℝ)) (1+1/Real.log X) k (index r) hXp
        ((scale_pos k).trans_le (index_range X hX2 k r hr).1) (by linarith [hδ.2]) hε1 hσ hscale).const_mul _).mono
          (fun x hx => hXp.trans_le hx.1)
    apply (hd.sub ht).congr
    intro x hx
    simp_rw [mul_sub]
    rw [integral_sub (density_discrete_integrable X s x δ (X^4) i j k hX hX2 hx hδ)
      (density_truncated_integrable X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) (X^4) i j k
        hX2 hx hδ hε1 hσ hσ2 hscale),discrete_integral_sum X s x δ i j k hX hX2 hx hδ,
      truncated_integral_sum X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k hX2 hx hδ hε1 hσ hσ2 hscale]
    rfl
  unfold centeredRemainder aggregate
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_finsetSum
  intro ij hij
  apply continuousOn_finsetSum
  intro k hk
  exact hi ij.1 ij.2 k hk

theorem centered_integrable (X s Y : ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hY : 0≤Y) (hYX : Y≤X/2) (hε : X^(-19/20:ℝ)∈Ioo 0 (1/4)) :
    IntegrableOn (fun x => centeredRemainder X s x (Y/X)) (Icc X (2*X)) := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  exact (centered_continuous X s (Y/X) hX hX2 hs hlog
    ⟨div_nonneg hY hXp.le,(div_le_iff₀ hXp).mpr (by linarith)⟩ hε).integrableOn_compact isCompact_Icc

run_cmd do
  for decl in [``truncated_integral_sum, ``scalar_continuous, ``centered_continuous, ``centered_integrable] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterCenteredSpatialWork
