import SourceFullTail
import SourceAbelLow
import MellinWindowFactor

/-!
v8. A complete all-frequency CENTERED SPECTRAL budget for the literal source.
UNCOMPILED DRAFT. The first-factor cap and a LOCAL relative psi-error remain
explicit. No full source energy, low/middle/tail energy, Fourier identity or
physical raw mean is assumed as a premise. The sharp Mellin window is the
original defined kernel, not an arbitrary multiplier.

This file does not assert the physical Parseval/change-of-variable theorem.
The remaining ordinary-function Fourier connection is kept separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 22000000
noncomputable section
open MeasureTheory Set
namespace SourceSpectralEnergy
open SourceFullTail SourceAbelLow SourceDyadicTail SourceCenteredMiddle
open SourceLiteralMiddle SourceLiteralMoments SourceMassDischarge SourceProductBlock
open PositiveInteriorModel PositiveInteriorCells

def spectralDensity (X δ : ℝ) (j : ℕ×ℕ) (t : ℝ) : ℝ :=
  ‖MellinWindowFactor.factor 1 δ t*centeredProduct X j t‖^2

 theorem density_continuous (X δ : ℝ) (j : ℕ×ℕ) (hX : 0<X) (hδ : δ<1) :
    Continuous (spectralDensity X δ j) :=
  ((MellinWindowFactor.continuous_factor 1 δ (by norm_num) hδ).mul
    (centered_continuous X j hX)).norm.pow 2

 theorem small_multiplier_bound (X δ t : ℝ) (j : ℕ×ℕ) (hδ0 : 0≤δ) (hδ1 : δ<1) :
    spectralDensity X δ j t≤δ^2*‖centeredProduct X j t‖^2 := by
  have hh := MellinWindowFactor.norm_le_width 1 δ t (by norm_num) hδ0 hδ1
  have hm := pow_le_pow_left₀ (norm_nonneg _) hh 2
  simpa only [spectralDensity,norm_mul,mul_pow] using
    mul_le_mul_of_nonneg_right hm (sq_nonneg (‖centeredProduct X j t‖))

 theorem high_multiplier_bound (X δ t : ℝ) (j : ℕ×ℕ)
    (hδ0 : 0≤δ) (hδ1 : δ<1) (ht : t≠0) :
    spectralDensity X δ j t≤4*(‖centeredProduct X j t‖^2/t^2) := by
  have hh := MellinWindowFactor.norm_le_frequency 1 δ t (by norm_num) hδ0 hδ1 ht
  have hm := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hh 2)
    (sq_nonneg (‖centeredProduct X j t‖))
  have he : (2/|t|)^2*‖centeredProduct X j t‖^2=4*(‖centeredProduct X j t‖^2/t^2) := by
    rw [div_pow,sq_abs]
    ring
  simpa only [spectralDensity,norm_mul,mul_pow,he] using hm

 theorem density_tail_integrable (X δ U : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hδ0 : 0≤δ) (hδ1 : δ<1) (hU : 1≤U) :
    IntegrableOn (spectralDensity X δ j) (outside U) := by
  have hm := (centered_tail_integrable X U j hX hlog hj hU).const_mul 4
  apply hm.mono' (density_continuous X δ j (by linarith) hδ1).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (outside_measurable U)] with t ht
  have ht0 : t≠0 := by intro he; simp [outside,he] at ht; linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ spectralDensity X δ j t from sq_nonneg _)]
  exact high_multiplier_bound X δ t j hδ0 hδ1 ht0

 theorem density_integrable (X δ U : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hδ0 : 0≤δ) (hδ1 : δ<1) (hU : 1≤U) :
    Integrable (spectralDensity X δ j) := by
  have hc : IntegrableOn (spectralDensity X δ j) (Icc (-U) U) :=
    (density_continuous X δ j (by linarith) hδ1).integrableOn_Icc
  have ht := density_tail_integrable X δ U j hX hlog hj hδ0 hδ1 hU
  have he : Icc (-U) U∪outside U=univ := by
    ext t
    simp only [mem_union,mem_Icc,outside,mem_setOf_eq,mem_univ,iff_true]
    by_cases hh : |t|≤U
    · exact Or.inl (abs_le.mp hh)
    · exact Or.inr (lt_of_not_ge hh)
  have hh := (integrableOn_union.mpr ⟨hc,ht⟩)
  rw [he] at hh
  simpa only [integrableOn_univ] using hh

/-- Source-centered low and middle pieces cover the whole finite frequency interval.
The overlap consists only of the two boundary points, but the proof merely
uses domination on a disjoint complement and does not need to delete atoms. -/
 theorem finite_energy (X T ε : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hT : 1≤T) (hTU : T≤height X) (hε : 0≤ε) (hpsi : LocalPsiError X j ε)
    (hsmall : ∀ t∈middle X T,
      ‖SourceLiteralMoments.factor X j 0 t‖≤(1+Real.log X)^(-26000:ℝ)) :
    (∫ t in Icc (-height X) (height X), ‖centeredProduct X j t‖^2) ≤
      19845000*ε^2*T^3+6*commonConstant/(1+Real.log X)^34+1620000/T := by
  let A := Icc (-height X) (height X)
  let B := Icc (-T) T
  let f : ℝ→ℝ := fun t => ‖centeredProduct X j t‖^2
  have hf : Continuous f := (centered_continuous X j (by linarith)).norm.pow 2
  have hBA : B⊆A := by
    intro t ht
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hs : A\B⊆middle X T := by
    intro t ht
    refine ⟨ht.1,?_⟩
    have hh : ¬ |t|≤T := by intro he; exact ht.2 (abs_le.mp he)
    exact (lt_of_not_ge hh).le
  have hAB : B∪(A\B)=A := by
    ext t
    constructor
    · rintro (ht | ht)
      · exact hBA ht
      · exact ht.1
    · intro ht
      by_cases hb : t∈B
      · exact Or.inl hb
      · exact Or.inr ⟨ht,hb⟩
  have hiA : IntegrableOn f A := hf.integrableOn_Icc
  have hiB : IntegrableOn f B := hf.integrableOn_Icc
  have hiS : IntegrableOn f (A\B) := hiA.mono_set sdiff_subset
  have hiM : IntegrableOn f (middle X T) := hiA.mono_set (middle_subset X T)
  have hdisc : Disjoint B (A\B) := by
    apply Set.disjoint_left.mpr
    intro t ht hs
    exact hs.2 ht
  have hpart : (∫ t in A, f t)=(∫ t in B, f t)+(∫ t in A\B, f t) := by
    have hh := setIntegral_union hdisc (measurableSet_Icc.diff measurableSet_Icc) hiB hiS
    rwa [hAB] at hh
  have hrest : (∫ t in A\B, f t)≤(∫ t in middle X T, f t) := by
    exact setIntegral_mono_set hiM (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall hs)
  have hl := low_energy X T ε j hX hlog hj hT hε hpsi
  have hm := centered_middle_of_first_factor_cap X T j hX hlog hj (by linarith) hsmall
  change (∫ t in A, f t)≤_
  rw [hpart]
  calc
    _ ≤ 19845000*ε^2*T^3+
        (6*commonConstant/(1+Real.log X)^34+1620000/T) :=
      add_le_add hl (hrest.trans hm)
    _ = _ := by ring

/-- An all-frequency estimate with only two exposed arithmetic inputs:
(1) the first literal polynomial cap; (2) a local relative psi-error.
All low/middle/tail integrals and their integrability are constructed. -/
 theorem all_frequency_budget (X T ε δ : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hT : 1≤T) (hTU : T≤height X) (hε : 0≤ε) (hδ0 : 0<δ) (hδ1 : δ<1)
    (hpsi : LocalPsiError X j ε)
    (hsmall : ∀ t∈middle X T,
      ‖SourceLiteralMoments.factor X j 0 t‖≤(1+Real.log X)^(-26000:ℝ)) :
    (∫ t, spectralDensity X δ j t)/δ^2 ≤
      19845000*ε^2*T^3+6*commonConstant/(1+Real.log X)^34+1620000/T+
      (4/δ^2)*(blockConstant*(1+Real.log X)^4*
        (8/(X*height X)+16/(3*(height X)^2))+270000/(height X)^3) := by
  have hU : 1≤height X := hT.trans hTU
  have hcentral := finite_energy X T ε j hX hlog hj hT hTU hε hpsi hsmall
  have htail := centered_tail X (height X) j hX hlog hj hU
  have hI := density_integrable X δ (height X) j hX hlog hj hδ0.le hδ1 hU
  have hIC : IntegrableOn (spectralDensity X δ j) (Icc (-height X) (height X)) :=
    (density_continuous X δ j (by linarith) hδ1).integrableOn_Icc
  have hG := (centered_continuous X j (by linarith)).norm.pow 2
  have hc := setIntegral_mono_on hIC (hG.integrableOn_Icc.const_mul (δ^2))
    measurableSet_Icc (fun t _ => small_multiplier_bound X δ t j hδ0.le hδ1)
  rw [integral_const_mul] at hc
  simp only [Pi.pow_apply] at hc
  have hGT := centered_tail_integrable X (height X) j hX hlog hj hU
  have ht := setIntegral_mono_on hI.integrableOn (hGT.const_mul 4)
    (outside_measurable (height X)) (by
      intro t ht
      have hn : t≠0 := by intro he; simp [outside,he] at ht; linarith
      exact high_multiplier_bound X δ t j hδ0.le hδ1 hn)
  rw [integral_const_mul] at ht
  have hcomp : (Icc (-height X) (height X))ᶜ=outside (height X) := by
    ext t
    change ¬(-height X ≤ t ∧ t ≤ height X) ↔ height X < |t|
    rw [←abs_le, not_le]
  have hsplit := integral_add_compl (s:=Icc (-height X) (height X)) measurableSet_Icc hI
  rw [hcomp] at hsplit
  apply (div_le_iff₀ (sq_pos_of_pos hδ0)).mpr
  have hcentral' := mul_le_mul_of_nonneg_left hcentral (sq_nonneg δ)
  have htail' := mul_le_mul_of_nonneg_left htail (by norm_num : (0:ℝ)≤4)
  have he : (19845000*ε^2*T^3+6*commonConstant/(1+Real.log X)^34+1620000/T+
      (4/δ^2)*(blockConstant*(1+Real.log X)^4*
        (8/(X*height X)+16/(3*(height X)^2))+270000/(height X)^3))*δ^2 =
      δ^2*(19845000*ε^2*T^3+6*commonConstant/(1+Real.log X)^34+1620000/T)+
      4*(blockConstant*(1+Real.log X)^4*
        (8/(X*height X)+16/(3*(height X)^2))+270000/(height X)^3) := by
    field_simp <;> ring
  rw [he]
  rw [←hsplit]
  exact add_le_add (hc.trans hcentral') (ht.trans htail')

/-- The requested local psi accuracy gives a fully explicit logarithmic budget.
This remains a spectral theorem, not an asserted physical Parseval identity. -/
 theorem literal_spectral_budget (X T Y : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hT : 1≤T) (hTU : T≤height X) (hY : 0<Y) (hYX : Y≤X/2)
    (hpsi : LocalPsiError X j (1/((1+Real.log X)^20*T^2)))
    (hsmall : ∀ t∈middle X T,
      ‖SourceLiteralMoments.factor X j 0 t‖≤(1+Real.log X)^(-26000:ℝ)) :
    (∫ t, spectralDensity X (Y/X) j t)/(Y/X)^2 ≤
      19845000/((1+Real.log X)^40*T)+
      6*commonConstant/(1+Real.log X)^34+1620000/T+
      32*blockConstant*(1+Real.log X)^4*X/(Y^2*height X)+
      (64/3)*blockConstant*(1+Real.log X)^4*X^2/(Y^2*(height X)^2)+
      1080000*X^2/(Y^2*(height X)^3) := by
  have hXp : 0<X := by linarith
  have hLp : 0<1+Real.log X := by linarith
  have hTp : 0<T := by linarith
  have hU : 0<height X := hTp.trans_le hTU
  have hδ : Y/X<1 := (div_lt_one hXp).mpr (by linarith)
  have hh := all_frequency_budget X T (1/((1+Real.log X)^20*T^2)) (Y/X) j
    hX hlog hj hT hTU (by positivity) (div_pos hY hXp) hδ hpsi hsmall
  convert hh using 1 <;> field_simp <;> ring

#print axioms literal_spectral_budget
run_cmd do
  for n in [``density_continuous,``small_multiplier_bound,``high_multiplier_bound,
      ``density_tail_integrable,``density_integrable,``finite_energy,
      ``all_frequency_budget,``literal_spectral_budget] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V8 FULL SPECTRAL BUDGET: TWO ARITHMETIC PREMISES REMAIN; NOT A PHYSICAL MEAN"
end SourceSpectralEnergy
