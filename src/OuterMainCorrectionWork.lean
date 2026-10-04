import OuterBlockSharpCompletionWork
import OuterLocalizedSeparatorCostWork
import PolynomialLogEnvelope

/-! Aggregate the exact main-mass normalization correction over every
selected block, source box and separator frequency. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterMainCorrectionWork
open OuterBlockMainTermWork OuterBlockMassBudgetWork OuterBlockCofactorScaleWork
open OuterActiveDyadicWork OuterSourceCubeIntegralWork OuterSourceDensityNormWork
open OuterPairSourceDecompositionWork MellinSmoothingFunction

def boxConstant (s : ℝ) (i j : ℕ) : ℝ :=
  (1+(Real.log 2)⁻¹)^4*(∏n : Fin 9,coordinateConstant s i j n)
def totalConstant (s : ℝ) : ℝ := ∑ij∈boxPairs s,boxConstant s ij.1 ij.2

def correctionBox (X s x δ ε σ : ℝ) (i j : ℕ) : ℂ :=
  ∑k∈activeKeys X s i j,∫ω, density X s i j ω *
    (continuousContour X s x δ ε σ i j k ω-((x*δ:ℝ):ℂ)*mainMass X s i j k ω)
      ∂frequencyCube (X^4)
def correction (X s x δ ε σ : ℝ) : ℂ :=
  ∑ij∈boxPairs s,correctionBox X s x δ ε σ ij.1 ij.2

theorem boxConstant_nonneg (s : ℝ) (i j : ℕ) : 0≤boxConstant s i j := by
  unfold boxConstant
  exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun n _ => coordinateConstant_nonneg s i j n))
theorem totalConstant_nonneg (s : ℝ) : 0≤totalConstant s :=
  Finset.sum_nonneg (fun ij _ => boxConstant_nonneg s ij.1 ij.2)

theorem density_integrable (X s T : ℝ) (i j : ℕ) :
    Integrable (density X s i j) (frequencyCube T) := by
  have hh := mode_integrable X s T i j (fun _ => 0)
  simpa [OuterMaskFrequencyWork.phase] using hh

theorem density_mass_integrable (X s T : ℝ) (i j : ℕ) (k : BlockKey) :
    Integrable (fun ω => density X s i j ω*mainMass X s i j k ω) (frequencyCube T) := by
  have he (ω : Fin 9→ℝ) : density X s i j ω*mainMass X s i j k ω =
      ∑r∈OuterRectangularBlocksWork.blockSource X k,
        ((OuterSmoothCoreWork.atomMultiplier X s i j r:ℂ)/(LongerTupleEncoding.index r:ℂ))*
        (density X s i j ω*OuterSeparatedFourierModeWork.sourceMode X s i j
          (OuterSourceReindexWork.drop r).1 r.1 (OuterSourceReindexWork.drop r).2.1
            (OuterSourceReindexWork.drop r).2.2 ω) := by
    simp only [mainMass,Finset.mul_sum,modeWeight]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  simp_rw [he]
  apply integrable_finsetSum
  intro r hr
  exact (mode_integrable X s T i j
    (OuterSmoothStepWork.signedGap (Real.log (r.1:ℝ))
      (OuterBufferedSourceWork.cutoffLogs X s (OuterSourceReindexWork.drop r) i j))).const_mul _

theorem density_correction_integrable (X s x δ ε σ T : ℝ) (i j : ℕ) (k : BlockKey)
    (hX : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 (1/4)) (hσ : 1<σ) (hσ2 : σ≤2)
    (hscale : 256*(OuterBlockCofactorWork.scale k:ℝ)≤X) :
    Integrable (fun ω => density X s i j ω*(continuousContour X s x δ ε σ i j k ω-
      ((x*δ:ℝ):ℂ)*mainMass X s i j k ω)) (frequencyCube T) := by
  have he (ω : Fin 9→ℝ) : density X s i j ω*(continuousContour X s x δ ε σ i j k ω-
      ((x*δ:ℝ):ℂ)*mainMass X s i j k ω) =
      (((x*δ:ℝ):ℂ)*(mellin (fun y => (Smooth1 smoothing ε y:ℂ)) 1-1))*
        (density X s i j ω*mainMass X s i j k ω) := by
    rw [continuousContour_eq X s x δ ε σ i j k ω hX hx hδ hε hσ hσ2 hscale]
    ring
  simp_rw [he]
  exact (density_mass_integrable X s T i j k).const_mul _

theorem box_bound (X s x δ ε σ C : ℝ) (i j : ℕ)
    (hX : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 (1/4)) (hσ : 1<σ) (hσ2 : σ≤2)
    (hclose : ‖mellin (fun y => (Smooth1 smoothing ε y:ℂ)) 1-1‖≤C*ε) :
    ‖correctionBox X s x δ ε σ i j‖≤C*ε*(x*δ)*boxConstant s i j*(1+Real.log X)^13 := by
  have hbudget : 0≤C*ε*(x*δ) :=
    mul_nonneg ((norm_nonneg _).trans hclose) (mul_nonneg (by linarith [hx.1]) hδ.1)
  have hb (k : BlockKey) (hk : k∈activeKeys X s i j) :
      ‖∫ω, density X s i j ω*(continuousContour X s x δ ε σ i j k ω-
        ((x*δ:ℝ):ℂ)*mainMass X s i j k ω) ∂frequencyCube (X^4)‖ ≤
      (C*ε*(x*δ))*(∫ω,‖density X s i j ω‖ ∂frequencyCube (X^4)) := by
    have hh := norm_integral_le_of_norm_le
      ((density_integrable X s (X^4) i j).norm.const_mul (C*ε*(x*δ)))
      (Filter.Eventually.of_forall (fun ω => show
        ‖density X s i j ω*(continuousContour X s x δ ε σ i j k ω-
          ((x*δ:ℝ):ℂ)*mainMass X s i j k ω)‖ ≤ (C*ε*(x*δ))*‖density X s i j ω‖ from by
        rw [norm_mul,mul_comm (C*ε*(x*δ))]
        exact mul_le_mul_of_nonneg_left
          (smoothing_error X s x δ ε σ C i j k ω hX hx hδ hε hσ hσ2
            (active_lower X s hX hs hlog i j k hk).1 hclose) (norm_nonneg _)))
    simpa only [integral_const_mul] using hh
  calc
    _ ≤ ∑k∈activeKeys X s i j, ‖∫ω,density X s i j ω*(continuousContour X s x δ ε σ i j k ω-
        ((x*δ:ℝ):ℂ)*mainMass X s i j k ω) ∂frequencyCube (X^4)‖ := norm_sum_le _ _
    _ ≤ ∑_k∈activeKeys X s i j,(C*ε*(x*δ))*(∫ω,‖density X s i j ω‖ ∂frequencyCube (X^4)) :=
      Finset.sum_le_sum hb
    _ = (C*ε*(x*δ))*(∑_k∈activeKeys X s i j,∫ω,‖density X s i j ω‖ ∂frequencyCube (X^4)) := by
      rw [Finset.mul_sum]
    _ ≤ (C*ε*(x*δ))*(boxConstant s i j*(1+Real.log X)^13) :=
      mul_le_mul_of_nonneg_left (OuterLocalizedSeparatorCostWork.selected_density_cost X s (X^4) hX i j) hbudget
    _ = _ := by ring

theorem full_bound (X s x δ ε σ C : ℝ)
    (hX : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 (1/4)) (hσ : 1<σ) (hσ2 : σ≤2)
    (hclose : ‖mellin (fun y => (Smooth1 smoothing ε y:ℂ)) 1-1‖≤C*ε) :
    ‖correction X s x δ ε σ‖≤C*ε*(x*δ)*totalConstant s*(1+Real.log X)^13 := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ij∈boxPairs s,C*ε*(x*δ)*boxConstant s ij.1 ij.2*(1+Real.log X)^13 :=
      Finset.sum_le_sum (fun ij _ => box_bound X s x δ ε σ C ij.1 ij.2 hX hs hlog hx hδ hε hσ hσ2 hclose)
    _ = _ := by simp only [totalConstant,Finset.mul_sum,Finset.sum_mul]

theorem eventually_full_correction (s : ℝ) (hs : 0≤s) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 2≤X ∧ ∀ (x Y σ : ℝ), x∈Icc X (2*X) →
      0≤Y → Y≤X/2 → 1<σ → σ≤2 →
      ‖correction X s x (Y/X) (X^(-19/20:ℝ)) σ‖≤Y/(Real.log X)^A := by
  obtain ⟨C,hC,ε₀,hε₀,hclose⟩ := CofactorMainTermBudget.multiplier_close
  have hεlim : Tendsto (fun X : ℝ => X^(-19/20:ℝ)) atTop (nhds 0) :=
    by simpa only [neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<19/20))
  have hcost : 0≤2*C*totalConstant s := by have := totalConstant_nonneg s; positivity
  filter_upwards [eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ)),
    hεlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4)),
    hεlim.eventually (gt_mem_nhds hε₀),
    PolynomialLogEnvelope.eventually_bound (2*C*totalConstant s) (13+A) (19/20) hcost (by norm_num)]
    with X hX hlog hε hεsmall hbudget
  refine ⟨hX,?_⟩
  intro x Y σ hx hY hYX hσ hσ2
  have hXp : 0<X := by linarith
  have hlp : 0<Real.log X := by linarith
  have hεp : 0<X^(-19/20:ℝ) := by positivity
  have hd : Y/X∈Icc (0:ℝ) (1/2) := ⟨div_nonneg hY hXp.le,(div_le_iff₀ hXp).mpr (by linarith)⟩
  have hm := full_bound X s x (Y/X) (X^(-19/20:ℝ)) σ C hX hs hlog hx hd
    ⟨hεp,hε⟩ hσ hσ2 (hclose _ hεp hεsmall)
  have hwidth : x*(Y/X)≤2*Y := by
    have hh := mul_le_mul_of_nonneg_right hx.2 (div_nonneg hY hXp.le)
    field_simp at hh ⊢
    nlinarith
  have hscalar : (2*C*totalConstant s)*(1+Real.log X)^13*X^(-19/20:ℝ)≤1/(Real.log X)^A := by
    apply (le_div_iff₀ (pow_pos hlp A)).mpr
    have hb : (2*C*totalConstant s)*(1+Real.log X)^13*(Real.log X)^A≤X^(19/20:ℝ) := by
      apply le_trans _ hbudget.2
      rw [pow_add, ←mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlp.le (by linarith : Real.log X≤1+Real.log X) A) (by positivity)
    have hh := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hXp.le (-19/20))
    have he : X^(-19/20:ℝ)*X^(19/20:ℝ)=1 := by rw [←Real.rpow_add hXp]; norm_num
    rw [he] at hh
    nlinarith
  calc
    _ ≤ _ := hm
    _ ≤ Y*((2*C*totalConstant s)*(1+Real.log X)^13*X^(-19/20:ℝ)) := by
      have hh := mul_le_mul_of_nonneg_left hwidth (show 0≤C*X^(-19/20:ℝ)*totalConstant s*(1+Real.log X)^13 by
        have := totalConstant_nonneg s; positivity)
      nlinarith
    _ ≤ Y*(1/(Real.log X)^A) := mul_le_mul_of_nonneg_left hscalar hY
    _ = _ := by ring

run_cmd do
  for decl in [``boxConstant_nonneg, ``totalConstant_nonneg, ``density_integrable,
      ``density_mass_integrable, ``density_correction_integrable, ``box_bound, ``full_bound, ``eventually_full_correction] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterMainCorrectionWork
