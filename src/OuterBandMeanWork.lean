import OuterBandRegularityWork
import OuterSharpContourAssemblyWork
import TripleFirstMean
import LongerTupleHigherMeanWork

/-! Spatial first means of actual centered bands, including every selected
block, source box, and separator frequency. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterBandMeanWork
open OuterUpperFrequencyWork OuterBandRegularityWork OuterMainCorrectionWork
open OuterActiveDyadicWork OuterBlockCofactorWork OuterSourceCubeIntegralWork
open OuterPairSourceDecompositionWork OuterSharpContourAssemblyWork

def blockBand (X s Y ε a b : ℝ) (i j : ℕ) (k : BlockKey) (x : ℝ) : ℂ :=
  ∫ω,density X s i j ω*band X s Y ε a b i j k ω x ∂frequencyCube (X^4)
def fullBand (X s Y ε a b x : ℝ) : ℝ :=
  (aggregate X s (fun i j k ω => band X s Y ε a b i j k ω x)).re

theorem block_integrable (X s Y ε a b : ℝ) (i j : ℕ) (k : BlockKey)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hYX : Y<X) (hε : ε∈Ioo 0 1)
    (hscale : 256*(scale k:ℝ)≤X) :
    IntegrableOn (blockBand X s Y ε a b i j k) (Icc X (2*X)) := by
  letI : SigmaFinite (frequencyCube (X^4)) := by unfold frequencyCube; infer_instance
  exact (joint_integrable X s Y ε a b (X^4) i j k hX hX2 hYX hε hscale).integral_prod_right

theorem full_integrable (X s Y ε a b : ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hYX : Y<X) (hε : ε∈Ioo 0 1) :
    IntegrableOn (fullBand X s Y ε a b) (Icc X (2*X)) := by
  unfold fullBand aggregate
  simp only [Complex.re_sum]
  apply integrable_finsetSum
  intro ij hij
  apply integrable_finsetSum
  intro k hk
  exact (block_integrable X s Y ε a b ij.1 ij.2 k hX hX2 hYX hε
    (OuterBlockCofactorScaleWork.active_lower X s hX2 hs hlog ij.1 ij.2 k hk).1).re

theorem block_mean_le (X s Y ε a b B : ℝ) (i j : ℕ) (k : BlockKey)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hYX : Y<X) (hε : ε∈Ioo 0 1)
    (hscale : 256*(scale k:ℝ)≤X)
    (hm : ∀ω,(1/X)*(∫x in Icc X (2*X),‖band X s Y ε a b i j k ω x‖)≤B) :
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
      apply integral_mono (hJ.integral_prod_left.const_mul _) ((density_integrable X s (X^4) i j).norm.const_mul B)
      intro ω
      simp only [norm_mul,integral_const_mul]
      have hh := mul_le_mul_of_nonneg_left (hm ω) (norm_nonneg (density X s i j ω))
      nlinarith only [hh]
    _ = _ := integral_const_mul _ _

theorem full_mean_le (X s Y ε a b B : ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hYX : Y<X) (hε : ε∈Ioo 0 1) (hB : 0≤B)
    (hm : ∀i j k,k∈activeKeys X s i j → ∀ω,
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
        exact block_mean_le X s Y ε a b B i j k hX hX2 hYX hε
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

theorem eventually_upper_first (s : ℝ) (hs : 0≤s) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1≤X ∧ 256≤X ∧ ∀(Y ε a b : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ),
      k∈activeKeys X s i j → X^(1009/10000:ℝ)≤Y → Y<X → ε∈Ioo 0 1 →
      a≤b → b-a≤X → (∀t∈Icc a b,X^(1124/1250:ℝ)≤|t|) →
      (1/X)*(∫x in Icc X (2*X),‖band X s Y ε a b i j k ω x‖)≤Y*X^(-1/20000:ℝ) := by
  filter_upwards [eventually_active_upper_square s hs,eventually_ge_atTop (Real.exp 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ))] with X hm hX hlog
  refine ⟨hX,hm.1,?_⟩
  intro Y ε a b i j k ω hk hY hYX hε hab hlen haway
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hYp : 0<Y := (Real.rpow_pos_of_pos hXp _).trans_le hY
  have hscale := (OuterBlockCofactorScaleWork.active_lower X s (by linarith [hm.1]) hs hlog i j k hk).1
  have hc := (band_continuous X s Y ε a b i j k ω hX (by linarith [hm.1]) hYX hε hscale).mono
    (show Icc X (2*X)⊆Ioi 0 from fun x hx => hXp.trans_le hx.1)
  have he : (Y*X^(-1/20000:ℝ))^2=Y^2*X^(-1/10000:ℝ) := by
    rw [mul_pow,←Real.rpow_mul_natCast hXp.le]
    norm_num
  have hh := TripleFirstMean.absolute_mean_le (fun x => ‖band X s Y ε a b i j k ω x‖)
    X (Y*X^(-1/20000:ℝ)) hXp (by positivity)
    (hc.norm.integrableOn_compact isCompact_Icc) ((hc.norm.pow 2).integrableOn_compact isCompact_Icc)
    (by rw [he]; exact hm.2 Y ε a b i j k ω hk hY hYX hε hab hlen haway)
  simpa only [abs_norm] using hh

theorem eventually_full_upper (s : ℝ) (hs : 0≤s) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 256≤X ∧ ∀Y ε a b : ℝ,
      X^(1009/10000:ℝ)≤Y → Y<X → ε∈Ioo 0 1 → a≤b → b-a≤X →
      (∀t∈Icc a b,X^(1124/1250:ℝ)≤|t|) →
      (1/X)*(∫x in Icc X (2*X),|fullBand X s Y ε a b x|)≤Y/(Real.log X)^A := by
  filter_upwards [eventually_upper_first s hs,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ)),
    PolynomialLogEnvelope.eventually_bound (totalConstant s) (13+A) (1/20000)
      (totalConstant_nonneg s) (by norm_num)] with X hm hlog hbudget
  refine ⟨hm.2.1,?_⟩
  intro Y ε a b hY hYX hε hab hlen haway
  have hXp : 0<X := (Real.exp_pos 1).trans_le hm.1
  have hY0 : 0≤Y := (Real.rpow_nonneg hXp.le _).trans hY
  have hl : 0<Real.log X := by linarith
  have hh := full_mean_le X s Y ε a b (Y*X^(-1/20000:ℝ)) hm.1
    (by linarith [hm.2.1]) hs hlog hYX hε (by positivity)
    (fun i j k hk ω => hm.2.2 Y ε a b i j k ω hk hY hYX hε hab hlen haway)
  apply hh.trans
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hb : totalConstant s*(1+Real.log X)^13*(Real.log X)^A≤X^(1/20000:ℝ) := by
    apply le_trans _ hbudget.2
    rw [pow_add,←mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le (by linarith) A)
      (by have := totalConstant_nonneg s; positivity)
  have hp : X^(-1/20000:ℝ)*X^(1/20000:ℝ)=1 := by rw [←Real.rpow_add hXp]; norm_num
  have hh := mul_le_mul_of_nonneg_left hb (show 0≤Y*X^(-1/20000:ℝ) by positivity)
  calc
    _ = (Y*X^(-1/20000:ℝ))*(totalConstant s*(1+Real.log X)^13*(Real.log X)^A) := by ring
    _ ≤ (Y*X^(-1/20000:ℝ))*X^(1/20000:ℝ) := hh
    _ = Y := by rw [mul_assoc,hp,mul_one]

run_cmd do
  for decl in [``block_integrable, ``full_integrable, ``block_mean_le, ``full_mean_le, ``eventually_upper_first, ``eventually_full_upper] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBandMeanWork
