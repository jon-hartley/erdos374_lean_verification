import SourceProfileConvolution
import SourceSpectralEnergy
import Mathlib.Tactic

/-! v9. Full literal source transform, not just the elementary kernels.
UNCOMPILED DRAFT. Ordered triples and all product collisions stay in the sums.
Qualitative L1/boundedness/a.e.-continuity are proved from the finite profile,
independently of any arithmetic cancellation or small source mean.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace SourceLiteralTransform
open SourceWindowFourier SourceAngularConvolution SourceProfileConvolution
open SourceLogWindow SourceLiteralMoments SourceLiteralMass SourceLiteralMiddle
open SourceReferenceSigmaOne SourceCenteredMiddle SourceSpectralEnergy
open PositiveSharpCounts PositiveInteriorModel PositiveInteriorCells
open CancellationTransferEndpoints Erdos374.HarmanGram152 MellinWindowFactor

def phase (t u : ℝ) : ℂ := Complex.exp (-Complex.I*(t:ℂ)*(u:ℂ))
def atomCoefficient (k : Triple) : ℂ := (tripleWeight k/tripleProduct k:ℝ)
def pairCoefficient (p r : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt p*ArithmeticFunction.vonMangoldt r/((p:ℝ)*(r:ℝ)):ℝ)
def profile (X : ℝ) (j : ℕ×ℕ) (ρ u : ℝ) : ℂ := centeredProfile X j ρ u

theorem profile_expansion (X ρ u : ℝ) (j : ℕ×ℕ) :
    profile X j ρ u =
      (∑ k∈sourceCoordinates X j, atomCoefficient k*kernelC ρ (u-Real.log (tripleProduct k))) -
      ∑ p∈support X j 0, ∑ r∈support X j 1,
        pairCoefficient p r*referenceC ρ (thirdScale X j/8) (4*thirdScale X j)
          (u-Real.log ((p:ℝ)*(r:ℝ))) := by
  unfold profile centeredProfile discreteProfile referenceProfile
  push_cast
  simp only [atomCoefficient,pairCoefficient,kernelC,referenceC]
  push_cast
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    ring
  · apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro r _
    ring

theorem discrete_integrable (X ρ : ℝ) (j : ℕ×ℕ) :
    Integrable (fun u => ∑ k∈sourceCoordinates X j,
      atomCoefficient k*kernelC ρ (u-Real.log (tripleProduct k))) := by
  exact integrable_finsetSum _ (fun k _ =>
    ((kernel_integrable ρ).comp_sub_right _).const_mul _)

theorem reference_sum_integrable (X ρ : ℝ) (j : ℕ×ℕ)
    (hX : 0<X) (hρ : 0<ρ) (hρ1 : ρ<1) :
    Integrable (fun u => ∑ p∈support X j 0, ∑ r∈support X j 1,
      pairCoefficient p r*referenceC ρ (thirdScale X j/8) (4*thirdScale X j)
        (u-Real.log ((p:ℝ)*(r:ℝ)))) := by
  have hL : 0<thirdScale X j := by unfold thirdScale PositiveInteriorModel.scale; positivity
  apply integrable_finsetSum
  intro p _
  apply integrable_finsetSum
  intro r _
  exact ((SourceProfileConvolution.reference_integrable ρ _ _ hρ hρ1
    (by positivity) (by linarith)).comp_sub_right _).const_mul _

theorem profile_integrable (X ρ : ℝ) (j : ℕ×ℕ)
    (hX : 0<X) (hρ : 0<ρ) (hρ1 : ρ<1) : Integrable (profile X j ρ) := by
  rw [funext (fun u => profile_expansion X ρ u j)]
  exact (discrete_integrable X ρ j).sub (reference_sum_integrable X ρ j hX hρ hρ1)

theorem profile_measurable (X ρ : ℝ) (j : ℕ×ℕ) : Measurable (profile X j ρ) := by
  rw [funext (fun u => profile_expansion X ρ u j)]
  apply Measurable.sub
  · apply Finset.measurable_fun_sum
    intro k _
    exact measurable_const.mul ((kernel_measurable ρ).comp (measurable_id.sub_const _))
  · apply Finset.measurable_fun_sum
    intro p _
    apply Finset.measurable_fun_sum
    intro r _
    exact measurable_const.mul ((SourceProfileConvolution.reference_continuous ρ _ _).measurable.comp
      (measurable_id.sub_const _))

/-- The bound is an explicitly finite coefficient mass; no smallness is claimed. -/
def profileCap (X : ℝ) (j : ℕ×ℕ) : ℝ :=
  (∑ k∈sourceCoordinates X j, ‖atomCoefficient k‖)+
    ∑ p∈support X j 0, ∑ r∈support X j 1, ‖pairCoefficient p r‖

theorem profileCap_nonneg (X : ℝ) (j : ℕ×ℕ) : 0≤profileCap X j := by
  unfold profileCap
  positivity

theorem profile_norm_le (X ρ u : ℝ) (j : ℕ×ℕ) (hX : 0<X) :
    ‖profile X j ρ u‖≤profileCap X j := by
  have hL : 0<thirdScale X j := by unfold thirdScale PositiveInteriorModel.scale; positivity
  rw [profile_expansion]
  apply (norm_sub_le _ _).trans
  unfold profileCap
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_left (kernel_norm_le_one ρ _) (norm_nonneg (atomCoefficient k))
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro p _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro r _
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_left (reference_norm_le_one ρ _ _ _ (by positivity))
      (norm_nonneg (pairCoefficient p r))

theorem shifted_kernel_ae_continuous (ρ v : ℝ) :
    ∀ᵐ u : ℝ, ContinuousAt (fun x => kernelC ρ (x-v)) u := by
  filter_upwards [volume.ae_ne v,
    volume.ae_ne (v-Real.log ρ)] with u hu0 huh
  have h0 : u-v≠0 := sub_ne_zero.mpr hu0
  have h1 : u-v≠ -Real.log ρ := by intro h; apply huh; linarith
  exact (kernel_continuousAt ρ (u-v) h0 h1).comp (f := fun x : ℝ => x-v) (continuous_id.sub continuous_const).continuousAt

theorem profile_ae_continuous (X ρ : ℝ) (j : ℕ×ℕ) :
    ∀ᵐ u : ℝ, ContinuousAt (profile X j ρ) u := by
  have hall : ∀ᵐ u : ℝ, ∀ k : Triple,
      ContinuousAt (fun x => atomCoefficient k*kernelC ρ (x-Real.log (tripleProduct k))) u := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [shifted_kernel_ae_continuous ρ (Real.log (tripleProduct k))] with u hu
    exact continuousAt_const.mul hu
  filter_upwards [hall] with u hu
  rw [funext (fun u => profile_expansion X ρ u j)]
  apply ContinuousAt.sub
  · exact tendsto_finsetSum _ (fun k _ => hu k)
  · have hc : Continuous (fun x => ∑ p∈support X j 0, ∑ r∈support X j 1,
        pairCoefficient p r*referenceC ρ (thirdScale X j/8) (4*thirdScale X j)
          (x-Real.log ((p:ℝ)*(r:ℝ)))) := by
      apply continuous_finset_sum
      intro p _
      apply continuous_finset_sum
      intro r _
      exact continuous_const.mul ((SourceProfileConvolution.reference_continuous ρ _ _).comp
        (continuous_id.sub continuous_const))
    exact hc.continuousAt

/-- Positive real bases: the physical reciprocal is not accidentally omitted. -/
theorem phase_div (v t : ℝ) (hv : 0<v) :
    phase t (Real.log v)/(v:ℂ) = (v:ℂ)^(-line 1 t) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hv.ne'),
    ←Complex.ofReal_log hv.le]
  have hexp : Complex.exp (-(Real.log v:ℂ))=(v:ℂ)⁻¹ := by
    rw [←Complex.ofReal_neg,←Complex.ofReal_exp,Real.exp_neg,Real.exp_log hv,
      Complex.ofReal_inv]
  have he : (Real.log v:ℂ)*(-line 1 t)=
      -(Real.log v:ℂ)+(-Complex.I*(t:ℂ)*(Real.log v:ℂ)) := by simp only [line, Complex.ofReal_one]; ring
  rw [he,Complex.exp_add,hexp]
  unfold phase
  ring

theorem positive_cpow_mul (a b : ℝ) (z : ℂ) (ha : 0<a) (hb : 0<b) :
    ((a*b:ℝ):ℂ)^z=(a:ℂ)^z*(b:ℂ)^z := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos ha hb).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne'),
    ←Complex.ofReal_log (mul_pos ha hb).le,←Complex.ofReal_log ha.le,
    ←Complex.ofReal_log hb.le,Real.log_mul ha.ne' hb.ne',Complex.ofReal_add,add_mul,
    Complex.exp_add]

theorem triple_phase (X t : ℝ) (j : ℕ×ℕ) (k : Triple) (hk : k∈sourceCoordinates X j) :
    atomCoefficient k*phase t (Real.log (tripleProduct k)) =
      (SourceMassDischarge.mangoldt k.1*(k.1:ℂ)^(-line 1 t))*
      (SourceMassDischarge.mangoldt k.2.1*(k.2.1:ℂ)^(-line 1 t))*
      (SourceMassDischarge.mangoldt k.2.2*(k.2.2:ℂ)^(-line 1 t)) := by
  rw [sourceCoordinates_eq] at hk
  obtain ⟨hp,hrq⟩ := Finset.mem_product.mp hk
  obtain ⟨hr,hq⟩ := Finset.mem_product.mp hrq
  have hp0 : (0:ℝ)<k.1 := by exact_mod_cast support_pos X j 0 k.1 hp
  have hr0 : (0:ℝ)<k.2.1 := by exact_mod_cast support_pos X j 1 k.2.1 hr
  have hq0 : (0:ℝ)<k.2.2 := by exact_mod_cast support_pos X j 2 k.2.2 hq
  have hprod : 0<tripleProduct k := by unfold tripleProduct; positivity
  have he : atomCoefficient k*phase t (Real.log (tripleProduct k)) =
      (tripleWeight k:ℂ)*(phase t (Real.log (tripleProduct k))/(tripleProduct k:ℂ)) := by
    unfold atomCoefficient
    push_cast
    ring
  rw [he,phase_div _ _ hprod]
  unfold tripleProduct
  rw [positive_cpow_mul _ _ _ (mul_pos hp0 hr0) hq0,positive_cpow_mul _ _ _ hp0 hr0]
  unfold tripleWeight SourceMassDischarge.mangoldt
  push_cast
  ring

theorem pair_phase (X t : ℝ) (j : ℕ×ℕ) (p r : ℕ)
    (hp : p∈support X j 0) (hr : r∈support X j 1) :
    pairCoefficient p r*phase t (Real.log ((p:ℝ)*(r:ℝ))) =
      (SourceMassDischarge.mangoldt p*(p:ℂ)^(-line 1 t))*
      (SourceMassDischarge.mangoldt r*(r:ℂ)^(-line 1 t)) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast support_pos X j 0 p hp
  have hr0 : (0:ℝ)<r := by exact_mod_cast support_pos X j 1 r hr
  have he : pairCoefficient p r*phase t (Real.log ((p:ℝ)*(r:ℝ))) =
      ((ArithmeticFunction.vonMangoldt p*ArithmeticFunction.vonMangoldt r:ℝ):ℂ)*
      (phase t (Real.log ((p:ℝ)*(r:ℝ)))/(((p:ℝ)*(r:ℝ)):ℂ)) := by
    unfold pairCoefficient
    push_cast
    ring
  rw [he, ←Complex.ofReal_mul, phase_div _ _ (mul_pos hp0 hr0),positive_cpow_mul _ _ _ hp0 hr0]
  unfold SourceMassDischarge.mangoldt
  push_cast
  ring

/-- Exact angular transform of the ORIGINAL centered source profile. -/
theorem profile_transform (X ρ t : ℝ) (j : ℕ×ℕ)
    (hX : 0<X) (hρ : 0<ρ) (hρ1 : ρ<1) :
    angular (profile X j ρ) t =
      MellinWindowFactor.factor 1 (1-ρ) t*centeredProduct X j t := by
  have hL : 0<thirdScale X j := by unfold thirdScale PositiveInteriorModel.scale; positivity
  rw [funext (fun u => profile_expansion X ρ u j)]
  rw [angular_sub _ _ (discrete_integrable X ρ j)
    (reference_sum_integrable X ρ j hX hρ hρ1)]
  rw [angular_finset_sum _ _ (fun k _ =>
    ((kernel_integrable ρ).comp_sub_right _).const_mul _)]
  have hD : (∑ k∈sourceCoordinates X j,
      angular (fun u => atomCoefficient k*kernelC ρ (u-Real.log (tripleProduct k))) t) =
      MellinWindowFactor.factor 1 (1-ρ) t*sourceProduct X j t := by
    simp_rw [angular_const_mul, SourceWindowFourier.translate, kernel_transform ρ t hρ hρ1]
    have he : (∑ k∈sourceCoordinates X j,
        atomCoefficient k*phase t (Real.log (tripleProduct k)))=sourceProduct X j t := by
      simp_rw [Finset.sum_congr rfl (fun k hk => triple_phase X t j k hk)]
      rw [sourceCoordinates_eq]
      simp only [Finset.sum_product,sourceProduct,SourceLiteralMoments.factor,
        verticalDirichlet152,line,Complex.ofReal_one,mul_assoc]
      simp only [Finset.sum_mul_sum]
      simp only [Finset.mul_sum,mul_assoc]
    change (∑ k∈sourceCoordinates X j, atomCoefficient k*
      (phase t (Real.log (tripleProduct k))*MellinWindowFactor.factor 1 (1-ρ) t))=_
    simp_rw [←mul_assoc,←Finset.sum_mul]
    rw [he,mul_comm]
  rw [hD]
  have hR : angular (fun u => ∑ p∈support X j 0, ∑ r∈support X j 1,
      pairCoefficient p r*referenceC ρ (thirdScale X j/8) (4*thirdScale X j)
        (u-Real.log ((p:ℝ)*(r:ℝ)))) t =
      MellinWindowFactor.factor 1 (1-ρ) t*referenceProduct X j t := by
    have hi := SourceProfileConvolution.reference_integrable ρ (thirdScale X j/8)
      (4*thirdScale X j) hρ hρ1 (by positivity) (by linarith)
    rw [angular_finset_sum _ _ (fun p _ => integrable_finsetSum _
      (fun r _ => (hi.comp_sub_right _).const_mul _))]
    simp_rw [angular_finset_sum _ _ (fun r _ => (hi.comp_sub_right _).const_mul _),
      angular_const_mul,SourceWindowFourier.translate,
      SourceProfileConvolution.reference_transform ρ (thirdScale X j/8) (4*thirdScale X j) t hρ hρ1 (by positivity) (by linarith)]
    have he : (∑ p∈support X j 0, ∑ r∈support X j 1,
        pairCoefficient p r*phase t (Real.log ((p:ℝ)*(r:ℝ))))=
        SourceLiteralMoments.factor X j 0 t*SourceLiteralMoments.factor X j 1 t := by
      simp only [SourceLiteralMoments.factor,verticalDirichlet152,Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro r hr
      simpa only [line,Complex.ofReal_one] using pair_phase X t j p r hp hr
    change (∑ p∈support X j 0, ∑ r∈support X j 1,
      pairCoefficient p r*(phase t (Real.log ((p:ℝ)*(r:ℝ)))*
        (MellinWindowFactor.factor 1 (1-ρ) t*thirdReference X j t)))=_
    simp_rw [←mul_assoc,←Finset.sum_mul]
    rw [he]
    unfold referenceProduct
    ring
  rw [hR]
  unfold centeredProduct
  ring

/-- Fourier-square integrability is supplied by v8's qualitative theorem;
no prime cap, local PNT error, or small spectral budget is used for regularity. -/
theorem profile_parseval (X Y : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (hY : 0<Y) (hYX : Y≤X/2) :
    (∫ u : ℝ, ‖profile X j (1-Y/X) u‖^2) =
      (1/(2*Real.pi))*(∫ t : ℝ, spectralDensity X (Y/X) j t) := by
  have hXp : 0<X := by linarith
  have hδ : 0<Y/X ∧ Y/X<1 := ⟨div_pos hY hXp,(div_lt_one hXp).mpr (by linarith)⟩
  have hρ : 0<1-Y/X ∧ 1-Y/X<1 := by constructor <;> linarith [hδ.1,hδ.2]
  have hspec := density_integrable X (Y/X) 1 j hX hlog hj hδ.1.le hδ.2 (by norm_num)
  have hident (t : ℝ) : ‖angular (profile X j (1-Y/X)) t‖^2=spectralDensity X (Y/X) j t := by
    rw [profile_transform X (1-Y/X) t j hXp hρ.1 hρ.2]
    simp only [sub_sub_cancel,spectralDensity]
  have hFi : Integrable (fun t : ℝ => ‖angular (profile X j (1-Y/X)) t‖^2) := by
    simp_rw [hident]
    exact hspec
  have hh := angular_parseval (profile X j (1-Y/X)) (profileCap X j)
    (profile_measurable X _ j) (profile_integrable X _ j hXp hρ.1 hρ.2)
    (profileCap_nonneg X j) (fun u => profile_norm_le X _ u j hXp)
    (profile_ae_continuous X _ j) hFi
  simpa only [hident] using hh

#print axioms profile_transform
#print axioms profile_parseval
run_cmd do
  for n in [``profile_expansion,``discrete_integrable,``reference_sum_integrable,
      ``profile_integrable,``profile_measurable,``profileCap_nonneg,``profile_norm_le,
      ``shifted_kernel_ae_continuous,``profile_ae_continuous,``phase_div,
      ``positive_cpow_mul,``triple_phase,``pair_phase,``profile_transform,``profile_parseval] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V9 LITERAL TRANSFORM/PARSEVAL: VALID ONLY AFTER ACTUAL COMPILATION"
end SourceLiteralTransform



