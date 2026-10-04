import OuterSharpContourRegularityWork

/-! Sum the actual sharp-to-contour error over all source boxes, selected
blocks and separator frequencies. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterSharpContourAssemblyWork
open OuterSharpContourWork OuterSharpContourRegularityWork OuterCompletedCollectionWork
open OuterBlockSharpCompletionWork OuterBlockMainTermWork OuterCompletedRemainderWork
open OuterMainCorrectionWork OuterSourceCubeIntegralWork OuterActiveDyadicWork
open OuterPairSourceDecompositionWork OuterLocalizedCoreWork

def aggregate (X s : ℝ) (F : ℕ→ℕ→BlockKey→(Fin 9→ℝ)→ℂ) : ℂ :=
  ∑ij∈boxPairs s,∑k∈activeKeys X s ij.1 ij.2,
    ∫ω,density X s ij.1 ij.2 ω*F ij.1 ij.2 k ω ∂frequencyCube (X^4)

def sharpError (X s x δ : ℝ) : ℂ := aggregate X s
  (fun i j k ω => completedCount X s (x-x*δ) x i j k ω-discreteContour X s x δ i j k ω)

def contourRemainder (X s x δ : ℝ) : ℝ := (aggregate X s
  (fun i j k ω => discreteContour X s x δ i j k ω-
    continuousContour X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) i j k ω)).re

theorem aggregate_bound (X s B : ℝ) (hX : 2≤X) (hB : 0≤B)
    (F : ℕ→ℕ→BlockKey→(Fin 9→ℝ)→ℂ)
    (hF : ∀i j k, k∈activeKeys X s i j → ∀ω,‖F i j k ω‖≤B) :
    ‖aggregate X s F‖≤B*totalConstant s*(1+Real.log X)^13 := by
  have hb (i j : ℕ) :
      ‖∑k∈activeKeys X s i j,∫ω,density X s i j ω*F i j k ω ∂frequencyCube (X^4)‖≤
        B*boxConstant s i j*(1+Real.log X)^13 := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑_k∈activeKeys X s i j,B*(∫ω,‖density X s i j ω‖ ∂frequencyCube (X^4)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hh := norm_integral_le_of_norm_le
          ((density_integrable X s (X^4) i j).norm.const_mul B)
          (Filter.Eventually.of_forall (fun ω => show ‖density X s i j ω*F i j k ω‖≤B*‖density X s i j ω‖ from by
            rw [norm_mul,mul_comm B]
            exact mul_le_mul_of_nonneg_left (hF i j k hk ω) (norm_nonneg _)))
        simpa only [integral_const_mul] using hh
      _ = B*(∑_k∈activeKeys X s i j,∫ω,‖density X s i j ω‖ ∂frequencyCube (X^4)) := by rw [Finset.mul_sum]
      _ ≤ B*(boxConstant s i j*(1+Real.log X)^13) :=
        mul_le_mul_of_nonneg_left (OuterLocalizedSeparatorCostWork.selected_density_cost X s (X^4) hX i j) hB
      _ = _ := by ring
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ij∈boxPairs s,B*boxConstant s ij.1 ij.2*(1+Real.log X)^13 :=
      Finset.sum_le_sum (fun ij _ => hb ij.1 ij.2)
    _ = _ := by simp only [totalConstant,Finset.mul_sum,Finset.sum_mul]

theorem eventually_sharp_error (s : ℝ) (hs : 0≤s) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 256≤X ∧ ∀x δ : ℝ, x∈Icc X (2*X) → δ∈Icc 0 (1/2) →
      ‖sharpError X s x δ‖≤X^(1/10:ℝ)/(Real.log X)^A := by
  filter_upwards [eventually_active_sharp_contour s hs,
    PolynomialLogEnvelope.eventually_bound (8*totalConstant s) (13+A) (1/50)
      (mul_nonneg (by norm_num) (totalConstant_nonneg s)) (by norm_num)] with X hsharp hbudget
  refine ⟨hsharp.1,?_⟩
  intro x δ hx hδ
  have hXp : 0<X := by linarith [hsharp.1]
  have hl : 0<Real.log X := Real.log_pos (by linarith [hsharp.1])
  have hb := aggregate_bound X s (8*X^(2/25:ℝ)) (by linarith [hsharp.1]) (by positivity)
    (fun i j k ω => completedCount X s (x-x*δ) x i j k ω-discreteContour X s x δ i j k ω)
    (fun i j k hk ω => hsharp.2 x δ i j k ω hk hx hδ)
  apply hb.trans
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hm : (8*totalConstant s)*(1+Real.log X)^13*(Real.log X)^A≤X^(1/50:ℝ) := by
    apply le_trans _ hbudget.2
    rw [pow_add,←mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le (by linarith) A)
      (by have := totalConstant_nonneg s; positivity)
  have hh := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hXp.le (2/25))
  have he : X^(2/25:ℝ)*X^(1/50:ℝ)=X^(1/10:ℝ) := by rw [←Real.rpow_add hXp]; norm_num
  rw [he] at hh
  nlinarith

theorem completed_identity (X s x δ : ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2)) (hε : X^(-19/20:ℝ)∈Ioo 0 (1/4)) :
    completedRemainder X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X)-contourRemainder X s x δ =
      (sharpError X s x δ).re := by
  have hσ : 1<1+1/Real.log X := by
    have : 0<1/Real.log X := by positivity
    linarith
  have hσ2 : 1+1/Real.log X≤2 := by
    have := (div_le_one (by linarith : 0<Real.log X)).mpr (show 1≤Real.log X by linarith)
    linarith
  simp only [completedRemainder,completedBox,contourRemainder,sharpError,aggregate,
    Complex.re_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  apply Finset.sum_congr rfl
  intro k hk
  have hic := density_count_integrable X s x δ (X^4) ij.1 ij.2 k hX2 hx hδ
  have hid := density_discrete_integrable X s x δ (X^4) ij.1 ij.2 k hX hX2 hx hδ
  have him : Integrable (fun ω => density X s ij.1 ij.2 ω*
      continuousContour X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) ij.1 ij.2 k ω) (frequencyCube (X^4)) := by
    have hh := (density_correction_integrable X s x δ (X^(-19/20:ℝ)) (1+1/Real.log X) (X^4)
      ij.1 ij.2 k hX2 hx hδ hε hσ hσ2
      (OuterBlockCofactorScaleWork.active_lower X s hX2 hs hlog ij.1 ij.2 k hk).1).add
      ((density_mass_integrable X s (X^4) ij.1 ij.2 k).const_mul ((x*δ:ℝ):ℂ))
    convert hh using 1
    funext ω
    simp only [Pi.add_apply]
    ring
  simp_rw [mul_sub]
  rw [integral_sub hic him,integral_sub hid him,integral_sub hic hid]
  simp only [Complex.sub_re]
  ring

theorem eventually_localized_contour (s : ℝ) (hs : 0≤s) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 256≤X ∧ ∀x Y : ℝ, x∈Icc X (2*X) →
      X^(1/10:ℝ)≤Y → Y≤X/2 →
      |localizedRemainder X s (x-x*(Y/X)) x-contourRemainder X s x (Y/X)|≤2*Y/(Real.log X)^A := by
  have hεlim : Tendsto (fun X : ℝ => X^(-19/20:ℝ)) atTop (nhds 0) := by
    simpa only [neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<19/20))
  filter_upwards [eventually_sharp_error s hs A,eventually_completed_error s hs A,
    eventually_ge_atTop (Real.exp 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ)),
    hεlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))]
    with X hsharp hmain hX hlog hε
  refine ⟨hsharp.1,?_⟩
  intro x Y hx hY hYX
  have hXp : 0<X := by linarith [hsharp.1]
  have hY0 : 0≤Y := (Real.rpow_nonneg hXp.le _).trans hY
  have hδ : Y/X∈Icc (0:ℝ) (1/2) := ⟨div_nonneg hY0 hXp.le,(div_le_iff₀ hXp).mpr (by linarith)⟩
  have hσ : 1<1+1/Real.log X := by
    have : 0<1/Real.log X := by positivity
    linarith
  have hσ2 : 1+1/Real.log X≤2 := by
    have := (div_le_one (by linarith : 0<Real.log X)).mpr (show 1≤Real.log X by linarith)
    linarith
  have hm := hmain.2 x Y (1+1/Real.log X) hx hY0 hYX hσ hσ2
  have hh := hsharp.2 x (Y/X) hx hδ
  have hid := completed_identity X s x (Y/X) hX hmain.1 hs hlog hx hδ ⟨by positivity,hε⟩
  have ha := abs_sub_le (localizedRemainder X s (x-x*(Y/X)) x)
    (completedRemainder X s x (Y/X) (X^(-19/20:ℝ)) (1+1/Real.log X)) (contourRemainder X s x (Y/X))
  have hc : |completedRemainder X s x (Y/X) (X^(-19/20:ℝ)) (1+1/Real.log X)-contourRemainder X s x (Y/X)|≤Y/(Real.log X)^A := by
    rw [hid]
    exact (Complex.abs_re_le_norm _).trans (hh.trans (div_le_div_of_nonneg_right hY (by positivity)))
  exact (ha.trans (add_le_add hm hc)).trans_eq (by ring)

run_cmd do
  for decl in [``aggregate_bound, ``eventually_sharp_error, ``completed_identity, ``eventually_localized_contour] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSharpContourAssemblyWork
