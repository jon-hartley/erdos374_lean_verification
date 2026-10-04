import OuterUpperFrequencyWork
import OuterContourSpatialWork
import SmoothedWindowNorm

/-! Finite source expansion and product-space integrability for arbitrary
physical-frequency bands of the actual centered contour. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterBandRegularityWork
open OuterUpperFrequencyWork OuterCompletedEnergyWork OuterBlockMainTermWork
open OuterBlockCofactorWork OuterActiveDyadicWork OuterRectangularBlocksWork
open OuterSourceCubeIntegralWork OuterContourSpatialWork LongerTupleEncoding
open MellinSmoothingFunction OuterCenteredFlatWork Erdos374.HarmanGram152

def scalarMode (X σ : ℝ) (k : BlockKey) (n : ℕ) (t : ℝ) : ℂ :=
  verticalDirichlet152 {n} (fun _ => 1) σ t*centeredFlat (lower X k) (upper X k) σ t

def scalarBand (X Y ε a b : ℝ) (k : BlockKey) (n : ℕ) (x : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*SmoothedWindowTransfer.transform (scalarMode X (1+1/Real.log X) k n)
    smoothing ε a b (1+1/Real.log X) (Y/X) x

theorem scalarMode_continuous (X σ : ℝ) (k : BlockKey) (n : ℕ)
    (hX : 0<X) (hn : 0<n) (hσ : 1<σ) (hscale : 256*(scale k:ℝ)≤X) :
    Continuous (scalarMode X σ k n) := by
  have hlo := lower_pos X k hscale
  have hhi := lower_le_upper X k hX
  exact (NormalizedMeanSquare.continuous_vertical _ _ _ (by simpa)).mul
    (OuterModeContinuityWork.continuous_centeredFlat _ _ σ (by omega) (by omega) hσ)

theorem band_continuous (X s Y ε a b : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hYX : Y<X) (hε : ε∈Ioo 0 1)
    (hscale : 256*(scale k:ℝ)≤X) : ContinuousOn (band X s Y ε a b i j k ω) (Ioi 0) := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hlog : 1≤Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hσ : 1<1+1/Real.log X := lt_add_of_pos_right _ (by positivity)
  exact (SmoothedWindowRegularity.continuousOn_transform
    (centeredPolynomial X s (1+1/Real.log X) i j k ω) smoothing ε a b (1+1/Real.log X) (Y/X)
    (centered_continuous X s _ i j k ω hX2 hσ hscale) hε (by linarith) ((div_lt_one hXp).mpr hYX)
    differentiable nonnegative support mass_one).const_mul _

theorem scalarBand_continuous (X Y ε a b : ℝ) (k : BlockKey) (n : ℕ)
    (hX : Real.exp 1≤X) (hn : 0<n) (hYX : Y<X) (hε : ε∈Ioo 0 1)
    (hscale : 256*(scale k:ℝ)≤X) : ContinuousOn (scalarBand X Y ε a b k n) (Ioi 0) := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hlog : 1≤Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hσ : 1<1+1/Real.log X := lt_add_of_pos_right _ (by positivity)
  exact (SmoothedWindowRegularity.continuousOn_transform (scalarMode X (1+1/Real.log X) k n)
    smoothing ε a b (1+1/Real.log X) (Y/X) (scalarMode_continuous X _ k n hXp hn hσ hscale)
    hε (by linarith) ((div_lt_one hXp).mpr hYX) differentiable nonnegative support mass_one).const_mul _

theorem band_sum (X s Y ε a b x : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hx : 0<x) (hYX : Y<X) (hε : ε∈Ioo 0 1)
    (hscale : 256*(scale k:ℝ)≤X) :
    band X s Y ε a b i j k ω x = ∑r∈blockSource X k,modeWeight X s i j ω r*scalarBand X Y ε a b k (index r) x := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hlog : 1≤Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hσ : 1<1+1/Real.log X := lt_add_of_pos_right _ (by positivity)
  have hkernel := SmoothedWindowNorm.continuous_kernel ε (1+1/Real.log X) (Y/X) x hε
    (by linarith) hx ((div_lt_one hXp).mpr hYX)
  have hi (r : Representation) (hr : r∈blockSource X k) : IntegrableOn
      (fun t => scalarMode X (1+1/Real.log X) k (index r) t*SmoothedWindowNorm.kernel ε (1+1/Real.log X) (Y/X) x t) (Icc a b) :=
    ((scalarMode_continuous X _ k (index r) hXp ((scale_pos k).trans_le (index_range X hX2 k r hr).1)
      hσ hscale).mul hkernel).integrableOn_Icc
  have he (t : ℝ) : centeredPolynomial X s (1+1/Real.log X) i j k ω t =
      ∑r∈blockSource X k,modeWeight X s i j ω r*scalarMode X (1+1/Real.log X) k (index r) t := by
    simp only [centeredPolynomial,modePolynomial,Finset.sum_mul,scalarMode,verticalDirichlet152,
      Finset.sum_singleton,one_mul,MellinWindowFactor.line]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  unfold band scalarBand SmoothedWindowTransfer.transform
  simp_rw [he,Finset.sum_mul]
  have he' (r : Representation) (t : ℝ) : modeWeight X s i j ω r*scalarMode X (1+1/Real.log X) k (index r) t*
      mellin (fun u => (Smooth1 smoothing ε u:ℂ)) (MellinWindowFactor.line (1+1/Real.log X) t)*
      ((x:ℂ)^MellinWindowFactor.line (1+1/Real.log X) t-((x-x*(Y/X):ℝ):ℂ)^MellinWindowFactor.line (1+1/Real.log X) t) =
      modeWeight X s i j ω r*(scalarMode X (1+1/Real.log X) k (index r) t*
        SmoothedWindowNorm.kernel ε (1+1/Real.log X) (Y/X) x t) := by unfold SmoothedWindowNorm.kernel; ring
  simp_rw [he']
  rw [integral_finsetSum _ (fun r hr => (hi r hr).const_mul _)]
  simp only [integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [SmoothedWindowNorm.kernel,mul_assoc]
  ring

theorem frequency_integrable (X s Y ε a b x T : ℝ) (i j : ℕ) (k : BlockKey)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hx : 0<x) (hYX : Y<X) (hε : ε∈Ioo 0 1)
    (hscale : 256*(scale k:ℝ)≤X) :
    Integrable (fun ω => density X s i j ω*band X s Y ε a b i j k ω x) (frequencyCube T) := by
  simp_rw [band_sum X s Y ε a b x i j k _ hX hX2 hx hYX hε hscale,Finset.mul_sum]
  apply integrable_finsetSum
  intro r hr
  simpa only [OuterCompletedCollectionWork.weights,mul_assoc] using
    (density_weights_integrable X s T i j (r,0)).mul_const (scalarBand X Y ε a b k (index r) x)

theorem joint_integrable (X s Y ε a b T : ℝ) (i j : ℕ) (k : BlockKey)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hYX : Y<X) (hε : ε∈Ioo 0 1)
    (hscale : 256*(scale k:ℝ)≤X) :
    Integrable (fun z : (Fin 9→ℝ)×ℝ => density X s i j z.1*band X s Y ε a b i j k z.1 z.2)
      ((frequencyCube T).prod (volume.restrict (Icc X (2*X)))) := by
  letI : SigmaFinite (frequencyCube T) := by unfold frequencyCube; infer_instance
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hi : Integrable (fun z : (Fin 9→ℝ)×ℝ => ∑r∈blockSource X k,
      (density X s i j z.1*modeWeight X s i j z.1 r)*scalarBand X Y ε a b k (index r) z.2)
      ((frequencyCube T).prod (volume.restrict (Icc X (2*X)))) := by
    apply integrable_finsetSum
    intro r hr
    have hs : IntegrableOn (scalarBand X Y ε a b k (index r)) (Icc X (2*X)) := ((scalarBand_continuous X Y ε a b k (index r) hX
      ((scale_pos k).trans_le (index_range X hX2 k r hr).1) hYX hε hscale).mono
      (show Icc X (2*X)⊆Ioi 0 from fun x hx => hXp.trans_le hx.1)).integrableOn_compact isCompact_Icc
    exact (density_weights_integrable X s T i j (r,0)).mul_prod hs
  apply hi.congr
  have hmem : ∀ᵐ z : (Fin 9→ℝ)×ℝ ∂(frequencyCube T).prod (volume.restrict (Icc X (2*X))),z.2∈Icc X (2*X) :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)).mpr
      (Filter.Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Icc))
  filter_upwards [hmem] with z hz
  rw [band_sum X s Y ε a b z.2 i j k z.1 hX hX2 (hXp.trans_le hz.1) hYX hε hscale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

run_cmd do
  for decl in [``scalarMode_continuous, ``band_continuous, ``scalarBand_continuous,
      ``band_sum, ``frequency_integrable, ``joint_integrable] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBandRegularityWork
