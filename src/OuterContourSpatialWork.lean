import OuterSharpContourAssemblyWork
import SmoothedWindowRegularity

/-! Spatial regularity of the fully assembled contour remainder. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterContourSpatialWork
open OuterSharpContourWork OuterSharpContourRegularityWork OuterSharpContourAssemblyWork
open OuterCompletedCollectionWork OuterBlockMainTermWork OuterBlockSharpCompletionWork
open OuterMainCorrectionWork OuterActiveDyadicWork OuterSourceCubeIntegralWork
open Erdos374.HarmanGram152 MellinSmoothingFunction

theorem density_weights_integrable (X s T : ℝ) (i j : ℕ) (a : Entry) :
    Integrable (fun ω => density X s i j ω*weights X s i j ω a) (frequencyCube T) := by
  have hh := (mode_integrable X s T i j
    (OuterSmoothStepWork.signedGap (Real.log (a.1.1:ℝ))
      (OuterBufferedSourceWork.cutoffLogs X s (OuterSourceReindexWork.drop a.1) i j))).const_mul
        (OuterSmoothCoreWork.atomMultiplier X s i j a.1:ℂ)
  convert hh using 1
  funext ω
  simp only [weights,modeWeight,OuterSeparatedFourierModeWork.sourceMode]
  ring

theorem discrete_integral_sum (X s x δ : ℝ) (i j : ℕ) (k : BlockKey)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2)) :
    (∫ω,density X s i j ω*discreteContour X s x δ i j k ω ∂frequencyCube (X^4)) =
      ∑a∈entries X k,(∫ω,density X s i j ω*weights X s i j ω a ∂frequencyCube (X^4))*
        (((1/(2*Real.pi):ℝ):ℂ)*∫t in Icc (-X) X,
          singleKernel x δ (X^(-19/20:ℝ)) (1+1/Real.log X) (product a) t) := by
  simp_rw [discrete_sum X s x δ i j k _ hX hX2 hx hδ,Finset.mul_sum]
  have he (ω : Fin 9→ℝ) (a : Entry) (C : ℂ) : density X s i j ω*(weights X s i j ω a*C) =
      (density X s i j ω*weights X s i j ω a)*C := (mul_assoc _ _ _).symm
  simp_rw [he]
  rw [integral_finsetSum _ (fun a _ => (density_weights_integrable X s (X^4) i j a).mul_const _)]
  simp only [integral_mul_const]

theorem single_continuous (X δ : ℝ) (n : ℕ) (hn : 0<n)
    (hX : Real.exp 1≤X) (hδ : δ<1) :
    ContinuousOn (fun x => ((1/(2*Real.pi):ℝ):ℂ)*∫t in Icc (-X) X,
      singleKernel x δ (X^(-19/20:ℝ)) (1+1/Real.log X) n t) (Ioi (0:ℝ)) := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hlog : 1≤Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hε : X^(-19/20:ℝ)∈Ioo 0 1 := ⟨by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg ((Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hX) (by norm_num)⟩
  have hh := (SmoothedWindowRegularity.continuousOn_transform
    (verticalDirichlet152 {n} (fun _ => 1) (1+1/Real.log X)) smoothing
    (X^(-19/20:ℝ)) (-X) X (1+1/Real.log X) δ
    (NormalizedMeanSquare.continuous_vertical _ _ _ (by simpa)) hε (by positivity) hδ
    differentiable nonnegative support mass_one).const_mul ((1/(2*Real.pi):ℝ):ℂ)
  simpa only [SmoothedWindowTransfer.transform,verticalDirichlet152,Finset.sum_singleton,
    one_mul,singleKernel,MellinWindowFactor.line] using hh

theorem contour_continuous (X s δ : ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hδ : δ∈Icc 0 (1/2)) (hε : X^(-19/20:ℝ)∈Ioo 0 (1/4)) :
    ContinuousOn (fun x => contourRemainder X s x δ) (Icc X (2*X)) := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hσ : 1<1+1/Real.log X := by
    have : 0<1/Real.log X := by positivity
    linarith
  have hσ2 : 1+1/Real.log X≤2 := by
    have := (div_le_one (by linarith : 0<Real.log X)).mpr (show 1≤Real.log X by linarith)
    linarith
  have hi (i j : ℕ) (k : BlockKey) (hk : k∈activeKeys X s i j) :
      ContinuousOn (fun x => ∫ω,density X s i j ω*
        (discreteContour X s x δ i j k ω-
          continuousContour X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k ω) ∂frequencyCube (X^4))
        (Icc X (2*X)) := by
    have hdisc : ContinuousOn (fun x => ∑a∈entries X k,
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
    have hmain : ContinuousOn (fun x : ℝ => ((x*δ:ℝ):ℂ)*
        mellin (fun u => (Smooth1 smoothing (X^(-19/20:ℝ)) u:ℂ)) 1*
        (∫ω,density X s i j ω*mainMass X s i j k ω ∂frequencyCube (X^4))) (Icc X (2*X)) := by
      fun_prop
    apply (hdisc.sub hmain).congr
    intro x hx
    have he (ω : Fin 9→ℝ) : density X s i j ω*
        continuousContour X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k ω =
        (((x*δ:ℝ):ℂ)*mellin (fun u => (Smooth1 smoothing (X^(-19/20:ℝ)) u:ℂ)) 1)*
          (density X s i j ω*mainMass X s i j k ω) := by
      rw [continuousContour_eq X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k ω hX2 hx hδ hε hσ hσ2
        (OuterBlockCofactorScaleWork.active_lower X s hX2 hs hlog i j k hk).1]
      ring
    simp_rw [mul_sub,he]
    rw [integral_sub (density_discrete_integrable X s x δ (X^4) i j k hX hX2 hx hδ)
      ((density_mass_integrable X s (X^4) i j k).const_mul _),integral_const_mul,
      discrete_integral_sum X s x δ i j k hX hX2 hx hδ]
    rfl
  unfold contourRemainder aggregate
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_finsetSum
  intro ij hij
  apply continuousOn_finsetSum
  intro k hk
  exact hi ij.1 ij.2 k hk

theorem contour_integrable (X s Y : ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hY : 0≤Y) (hYX : Y≤X/2) (hε : X^(-19/20:ℝ)∈Ioo 0 (1/4)) :
    IntegrableOn (fun x => contourRemainder X s x (Y/X)) (Icc X (2*X)) := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  exact (contour_continuous X s (Y/X) hX hX2 hs hlog
    ⟨div_nonneg hY hXp.le,(div_le_iff₀ hXp).mpr (by linarith)⟩ hε).integrableOn_compact isCompact_Icc

run_cmd do
  for decl in [``density_weights_integrable, ``discrete_integral_sum, ``single_continuous,
      ``contour_continuous, ``contour_integrable] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterContourSpatialWork
