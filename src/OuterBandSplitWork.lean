import OuterBandMeanWork
import OuterCenteredTransformWork
import SmoothedFrequencySplit

/-! Exact band splitting for the complete centered source, retaining all
separator integrals and active blocks. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterBandSplitWork
open OuterBandMeanWork OuterUpperFrequencyWork OuterBandRegularityWork
open OuterCompletedEnergyWork OuterActiveDyadicWork OuterBlockCofactorWork
open OuterSharpContourAssemblyWork OuterCenteredContourWork OuterSourceCubeIntegralWork

theorem band_adjacent (X s Y ε a b c x : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hx : 0<x) (hYX : Y<X) (hε : ε∈Ioo 0 1)
    (hscale : 256*(scale k:ℝ)≤X) (hab : a≤b) (hbc : b≤c) :
    band X s Y ε a c i j k ω x=band X s Y ε a b i j k ω x+band X s Y ε b c i j k ω x := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hlog : 1≤Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hσ : 1<1+1/Real.log X := lt_add_of_pos_right _ (by positivity)
  unfold band
  rw [SmoothedFrequencySplit.adjacent _ ε a b c _ _ x
    (centered_continuous X s _ i j k ω hX2 hσ hscale) hε (by linarith) hx
    ((div_lt_one hXp).mpr hYX) hab hbc,mul_add]

theorem full_adjacent (X s Y ε a b c x : ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hx : 0<x) (hYX : Y<X) (hε : ε∈Ioo 0 1) (hab : a≤b) (hbc : b≤c) :
    fullBand X s Y ε a c x=fullBand X s Y ε a b x+fullBand X s Y ε b c x := by
  unfold fullBand aggregate
  simp only [Complex.re_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  apply Finset.sum_congr rfl
  intro k hk
  have hscale := (OuterBlockCofactorScaleWork.active_lower X s hX2 hs hlog ij.1 ij.2 k hk).1
  simp_rw [band_adjacent X s Y ε a b c x ij.1 ij.2 k _ hX hX2 hx hYX hε hscale hab hbc,mul_add]
  rw [integral_add
    (frequency_integrable X s Y ε a b x (X^4) ij.1 ij.2 k hX hX2 hx hYX hε hscale)
    (frequency_integrable X s Y ε b c x (X^4) ij.1 ij.2 k hX hX2 hx hYX hε hscale),Complex.add_re]

theorem centered_eq_full (X s Y x : ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hx : x∈Icc X (2*X)) (hY : 0≤Y) (hYX : Y≤X/2) :
    centeredRemainder X s x (Y/X)=fullBand X s Y (X^(-19/20:ℝ)) (-X) X x := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hδ : Y/X∈Icc (0:ℝ) (1/2) := ⟨div_nonneg hY hXp.le,(div_le_iff₀ hXp).mpr (by linarith)⟩
  unfold centeredRemainder fullBand aggregate
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  apply Finset.sum_congr rfl
  intro k hk
  apply integral_congr_ae
  filter_upwards with ω
  rw [OuterCenteredTransformWork.block_transform X s x (Y/X) ij.1 ij.2 k ω hX hX2 hx hδ
    (OuterBlockCofactorScaleWork.active_lower X s hX2 hs hlog ij.1 ij.2 k hk).1]
  rfl

theorem centered_three_bands (X s Y H x : ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hx : x∈Icc X (2*X)) (hY : 0≤Y) (hYX : Y≤X/2) (hH : 0≤H) (hHX : H≤X) :
    centeredRemainder X s x (Y/X)=
      fullBand X s Y (X^(-19/20:ℝ)) (-X) (-H) x+
      fullBand X s Y (X^(-19/20:ℝ)) (-H) H x+
      fullBand X s Y (X^(-19/20:ℝ)) H X x := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hε : X^(-19/20:ℝ)∈Ioo 0 1 := ⟨by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith : 1<X) (by norm_num)⟩
  have hxp : 0<x := hXp.trans_le hx.1
  have hYX' : Y<X := by linarith
  rw [centered_eq_full X s Y x hX hX2 hs hlog hx hY hYX,
    full_adjacent X s Y _ (-X) (-H) X x hX hX2 hs hlog hxp hYX' hε (by linarith) (by linarith),
    full_adjacent X s Y _ (-H) H X x hX hX2 hs hlog hxp hYX' hε (by linarith) hHX]
  ring

run_cmd do
  for decl in [``band_adjacent, ``full_adjacent, ``centered_eq_full, ``centered_three_bands] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBandSplitWork
