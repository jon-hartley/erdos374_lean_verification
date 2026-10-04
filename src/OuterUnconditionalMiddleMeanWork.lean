import OuterUnconditionalLiteralWork
import OuterBandMeanAEWork
import SmoothedWindowLogBudgetWork

/-! Unconditional full source and spatial assembly of the middle-band estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace OuterUnconditionalMiddleMeanWork
open OuterUnconditionalLiteralWork OuterBandMeanWork OuterBandMeanAEWork
open OuterUpperFrequencyWork OuterCompletedEnergyWork OuterMainCorrectionWork
open OuterActiveDyadicWork OuterBlockCofactorWork

theorem eventually_full_middle (s : ℝ) (hs : 0≤s) (A : ℕ) :
      ∀ᶠ X : ℝ in atTop,256≤X ∧ ∀Y ε a b : ℝ,
        0<Y → Y<X → ε∈Ioo 0 1 → 1≤b-a → b-a≤X^(1124/1250:ℝ) →
        (∀t∈Icc a b,X^(1/1000:ℝ)≤|t| ∧ |t|≤X^(1124/1250:ℝ)) →
        (1/X)*(∫x in Icc X (2*X),|fullBand X s Y ε a b x|)≤Y/(Real.log X)^A := by
  filter_upwards [eventually_literal_energy (2*(A+14)+2),
    SmoothedWindowLogBudgetWork.eventually_first momentConstant momentConstant_pos.le (A+14),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((2:ℝ)^13*totalConstant s))]
    with X he ht hlog hcost
  refine ⟨he.1,?_⟩
  intro Y ε a b hY hYX hε hlength hlen hband
  have hXp : 0<X := (Real.exp_pos 1).trans_le ht.1
  have hX : 2≤X := by linarith [he.1]
  have hl : 0<Real.log X := by linarith
  have hσ : 1<1+1/Real.log X := lt_add_of_pos_right _ (by positivity)
  have hHX : X^(1124/1250:ℝ)≤X := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤X)
      (show (1124/1250:ℝ)≤1 by norm_num)
  have hab : a≤b := by linarith
  have hm (i j : ℕ) (k : BlockKey) (hk : k∈activeKeys X s i j) :
      ∀ᵐ ω ∂OuterSourceCubeIntegralWork.frequencyCube (X^4),
        (1/X)*(∫x in Icc X (2*X),‖band X s Y ε a b i j k ω x‖)≤Y/(Real.log X)^(A+14) := by
    filter_upwards with ω
    exact ht.2 Y ε a b (centeredPolynomial X s (1+1/Real.log X) i j k ω) hY hYX hε hab (hlen.trans hHX)
      (centered_continuous X s _ i j k ω hX hσ (OuterBlockCofactorScaleWork.active_lower X s hX hs hlog i j k hk).1)
      (by
        have hh := he.2 s (1+1/Real.log X) a (b-a) i j k ω hs hk hσ hlength hlen
          (by
            intro t ht
            have hb : t∈Icc a b := by simpa only [add_sub_cancel] using ht
            exact ⟨(hband t hb).1, (hband t hb).2.trans hHX⟩)
        simpa only [add_sub_cancel] using hh)
  have hh := full_mean_le_ae X s Y ε a b (Y/(Real.log X)^(A+14)) ht.1 hX hs hlog hYX hε (by positivity) hm
  have hc : totalConstant s*(1+Real.log X)^13≤(Real.log X)^14 := by
    calc
      _ ≤ totalConstant s*(2*Real.log X)^13 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity : 0≤1+Real.log X) (by linarith : 1+Real.log X≤2*Real.log X) 13)
        (totalConstant_nonneg s)
      _ = (2^13*totalConstant s)*(Real.log X)^13 := by rw [mul_pow]; ring
      _ ≤ Real.log X*(Real.log X)^13 := mul_le_mul_of_nonneg_right hcost (by positivity)
      _ = _ := by ring
  apply hh.trans
  calc
    _ = (Y/(Real.log X)^(A+14))*(totalConstant s*(1+Real.log X)^13) := by ring
    _ ≤ (Y/(Real.log X)^(A+14))*(Real.log X)^14 := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [pow_add]; field_simp

run_cmd do
  for decl in [``eventually_full_middle] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterUnconditionalMiddleMeanWork
