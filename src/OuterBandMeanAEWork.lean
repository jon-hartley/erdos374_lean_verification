import OuterBandMeanWork

/-! The full band-mean transfer only needs mode estimates almost everywhere
on the actual finite separator cube, not at unbounded translations. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterBandMeanAEWork
open OuterBandMeanWork OuterUpperFrequencyWork OuterBandRegularityWork OuterMainCorrectionWork
open OuterActiveDyadicWork OuterBlockCofactorWork OuterSourceCubeIntegralWork
open OuterPairSourceDecompositionWork OuterSharpContourAssemblyWork

theorem ae_cube (T : ℝ) : ∀ᵐ ω ∂frequencyCube T,∀n,|ω n|≤T := by
  apply ae_all_iff.mpr
  intro n
  have hh : ∀ᵐ t : ℝ ∂volume.restrict (Ioc (-T) T),t∈Ioc (-T) T := ae_restrict_mem measurableSet_Ioc
  have he := Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin 9 => volume.restrict (Ioc (-T) T)) (i:=n) hh
  filter_upwards [he] with ω hω
  exact abs_le.mpr ⟨hω.1.le,hω.2⟩

theorem block_mean_le_ae (X s Y ε a b B : ℝ) (i j : ℕ) (k : BlockKey)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hYX : Y<X) (hε : ε∈Ioo 0 1)
    (hscale : 256*(scale k:ℝ)≤X)
    (hm : ∀ᵐ ω ∂frequencyCube (X^4),(1/X)*(∫x in Icc X (2*X),‖band X s Y ε a b i j k ω x‖)≤B) :
    (1/X)*(∫x in Icc X (2*X),|(blockBand X s Y ε a b i j k x).re|)≤
      B*(∫ω,‖density X s i j ω‖ ∂frequencyCube (X^4)) := by
  letI : SigmaFinite (frequencyCube (X^4)) := by unfold frequencyCube; infer_instance
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hJ := (joint_integrable X s Y ε a b (X^4) i j k hX hX2 hYX hε hscale).norm
  have hf := (block_integrable X s Y ε a b i j k hX hX2 hYX hε hscale).re.abs
  have hb := integral_mono hf hJ.integral_prod_right (fun x =>
    (Complex.abs_re_le_norm _).trans (norm_integral_le_integral_norm _))
  apply (mul_le_mul_of_nonneg_left hb (one_div_nonneg.mpr hXp.le)).trans
  rw [←integral_integral_swap hJ,←integral_const_mul]
  calc
    _ ≤ ∫ω,B*‖density X s i j ω‖ ∂frequencyCube (X^4) := by
      apply integral_mono_ae (hJ.integral_prod_left.const_mul _) ((density_integrable X s (X^4) i j).norm.const_mul B)
      filter_upwards [hm] with ω hω
      simp only [norm_mul,integral_const_mul]
      have hh := mul_le_mul_of_nonneg_left hω (norm_nonneg (density X s i j ω))
      nlinarith only [hh]
    _ = _ := integral_const_mul _ _

theorem full_mean_le_ae (X s Y ε a b B : ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hYX : Y<X) (hε : ε∈Ioo 0 1) (hB : 0≤B)
    (hm : ∀i j k,k∈activeKeys X s i j → ∀ᵐ ω ∂frequencyCube (X^4),
      (1/X)*(∫x in Icc X (2*X),‖band X s Y ε a b i j k ω x‖)≤B) :
    (1/X)*(∫x in Icc X (2*X),|fullBand X s Y ε a b x|)≤
      B*totalConstant s*(1+Real.log X)^13 := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hi (i j : ℕ) (k : BlockKey) (hk : k∈activeKeys X s i j) :=
    (block_integrable X s Y ε a b i j k hX hX2 hYX hε
      (OuterBlockCofactorScaleWork.active_lower X s hX2 hs hlog i j k hk).1).re
  have hb (i j : ℕ) : (1/X)*(∫x in Icc X (2*X),
      |∑k∈activeKeys X s i j,(blockBand X s Y ε a b i j k x).re|)≤
        B*boxConstant s i j*(1+Real.log X)^13 := by
    apply (LongerTupleHigherMeanWork.absolute_sum_mean_le _ _ X hXp (hi i j)).trans
    calc
      _ ≤ ∑k∈activeKeys X s i j,B*(∫ω,‖density X s i j ω‖ ∂frequencyCube (X^4)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact block_mean_le_ae X s Y ε a b B i j k hX hX2 hYX hε
          (OuterBlockCofactorScaleWork.active_lower X s hX2 hs hlog i j k hk).1 (hm i j k hk)
      _ = B*(∑_k∈activeKeys X s i j,∫ω,‖density X s i j ω‖ ∂frequencyCube (X^4)) := by rw [Finset.mul_sum]
      _ ≤ B*(boxConstant s i j*(1+Real.log X)^13) :=
        mul_le_mul_of_nonneg_left (OuterLocalizedSeparatorCostWork.selected_density_cost X s (X^4) hX2 i j) hB
      _ = _ := by ring
  unfold fullBand aggregate
  simp only [Complex.re_sum]
  apply (LongerTupleHigherMeanWork.absolute_sum_mean_le _ _ X hXp
    (fun ij _ => integrable_finsetSum _ (hi ij.1 ij.2))).trans
  calc
    _ ≤ ∑ij∈boxPairs s,B*boxConstant s ij.1 ij.2*(1+Real.log X)^13 := Finset.sum_le_sum (fun ij _ => hb ij.1 ij.2)
    _ = _ := by simp only [totalConstant,Finset.mul_sum,Finset.sum_mul]

run_cmd do
  for decl in [``ae_cube, ``block_mean_le_ae, ``full_mean_le_ae] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBandMeanAEWork
