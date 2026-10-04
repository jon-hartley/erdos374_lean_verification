import Item1SelectedWindow

/-! UNCOMPILED, 2026-10-02. Exact selected-source transform and qualitative
Fourier-square integrability. The full reference is inherited unchanged.
Small low/middle/tail estimates, arithmetic caps, and Parseval identities are NOT
premises of normalized_parseval. Its imported analytic proof bodies are drafts.
-/
set_option autoImplicit false
set_option maxHeartbeats 26000000
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace Item1SelectedFourier
open Item1SelectedWindow SourceWindowFourier SourceAngularConvolution
open SourceLiteralTransform SourceProfileConvolution SourceLogWindow
open SourceLiteralMoments SourceLiteralMass SourceReferenceSigmaOne
open PositiveInteriorModel PositiveInteriorCells CancellationTransferEndpoints PositiveSharpCounts
open Erdos374.HarmanGram152 MellinWindowFactor SourceDyadicTail

def spectrum (X : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple) (t : ℝ) : ℂ :=
  atomPolynomial S t-referenceProduct X j t

/-- Normalized energy: this multiplier INCLUDES division by eta=Y/X. -/
def normalizedMultiplier (eta t : ℝ) : ℂ := MellinWindowFactor.factor 1 eta t/(eta:ℂ)

def density (X Y : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple) (t : ℝ) : ℝ :=
  ‖normalizedMultiplier (Y/X) t*spectrum X j S t‖^2

def energy (X Y : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple) : ℝ :=
  ∫ t : ℝ, density X Y j S t

theorem atomPolynomial_continuous (S : Finset SourceTriple) :
    Continuous (atomPolynomial S) := by
  unfold atomPolynomial phase
  fun_prop

theorem atomPolynomial_bound (S : Finset SourceTriple) (t : ℝ) :
    ‖atomPolynomial S t‖ ≤ atomMass S := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  simp only [norm_mul,phase,phase_norm,mul_one]
  exact le_rfl

theorem atoms_transform (S : Finset SourceTriple) (rho t : ℝ)
    (hr0 : 0<rho) (hr1 : rho<1) :
    angular (atoms S rho) t=MellinWindowFactor.factor 1 (1-rho) t*atomPolynomial S t := by
  unfold atoms
  rw [angular_finset_sum _ _ (fun a _ =>
    ((kernel_integrable rho).comp_sub_right _).const_mul _)]
  simp_rw [angular_const_mul,SourceWindowFourier.translate,kernel_transform rho t hr0 hr1]
  change (∑ a ∈ S, atomCoefficient a*(phase t (Real.log (tripleProduct a))*
    MellinWindowFactor.factor 1 (1-rho) t)) = _
  simp_rw [←mul_assoc,←Finset.sum_mul]
  rw [mul_comm]
  rfl

/-- Extract the old full-reference calculation as an explicit reusable theorem. -/
theorem fullReference_transform (X rho t : ℝ) (j : ℕ × ℕ)
    (hX : 0<X) (hr0 : 0<rho) (hr1 : rho<1) :
    angular (fullReference X j rho) t =
      MellinWindowFactor.factor 1 (1-rho) t*referenceProduct X j t := by
  have hL : 0<thirdScale X j := by unfold thirdScale PositiveInteriorModel.scale; positivity
  have hi := SourceProfileConvolution.reference_integrable rho (thirdScale X j/8)
    (4*thirdScale X j) hr0 hr1 (by positivity) (by linarith)
  unfold fullReference
  rw [angular_finset_sum _ _ (fun p _ => integrable_finsetSum _
    (fun r _ => (hi.comp_sub_right _).const_mul _))]
  simp_rw [angular_finset_sum _ _ (fun r _ => (hi.comp_sub_right _).const_mul _),
    angular_const_mul,SourceWindowFourier.translate,
    SourceProfileConvolution.reference_transform rho (thirdScale X j/8) (4*thirdScale X j) t hr0 hr1 (by positivity) (by linarith)]
  have he : (∑ p ∈ support X j 0, ∑ r ∈ support X j 1,
      pairCoefficient p r*phase t (Real.log ((p:ℝ)*(r:ℝ))))=
      SourceLiteralMoments.factor X j 0 t*SourceLiteralMoments.factor X j 1 t := by
    simp only [SourceLiteralMoments.factor,verticalDirichlet152,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro r hr
    simpa only [line,Complex.ofReal_one] using pair_phase X t j p r hp hr
  change (∑ p ∈ support X j 0, ∑ r ∈ support X j 1,
    pairCoefficient p r*(phase t (Real.log ((p:ℝ)*(r:ℝ)))*
      (MellinWindowFactor.factor 1 (1-rho) t*thirdReference X j t))) = _
  simp_rw [←mul_assoc,←Finset.sum_mul]
  rw [he]
  unfold referenceProduct
  ring

theorem selected_transform (X rho t : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (hX : 0<X) (hr0 : 0<rho) (hr1 : rho<1) :
    angular (selectedProfile X j S rho) t =
      MellinWindowFactor.factor 1 (1-rho) t*spectrum X j S t := by
  unfold selectedProfile
  rw [angular_sub _ _ (atoms_integrable S rho)
    (fullReference_integrable X rho j hX hr0 hr1),
    atoms_transform S rho t hr0 hr1,fullReference_transform X rho t j hX hr0 hr1]
  unfold spectrum
  ring

theorem normalized_transform (X Y t : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (hX : 0<X) (hY : 0<Y) (hYX : Y≤X/2) :
    angular (normalizedProfile X Y j S) t =
      normalizedMultiplier (Y/X) t*spectrum X j S t := by
  have he0 : 0<Y/X := div_pos hY hX
  have he1 : Y/X≤1/2 := (div_le_iff₀ hX).mpr (by linarith)
  unfold normalizedProfile
  rw [angular_const_mul,
    selected_transform X (1-Y/X) t j S hX (by linarith) (by linarith)]
  simp only [sub_sub_cancel,normalizedMultiplier]
  ring

theorem spectrum_continuous (X : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (hX : 0<X) : Continuous (spectrum X j S) :=
  (atomPolynomial_continuous S).sub (SourceReferenceSigmaOne.reference_continuous X j hX)

/-- Qualitative boundedness on |t|>1. It does not claim prime cancellation. -/
theorem spectrum_outside_bound (X t : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (ht : t∈outside 1) : ‖spectrum X j S t‖ ≤ atomMass S+450 := by
  have ht1 : 1< |t| := ht
  have ht0 : t≠0 := by intro he; norm_num [he] at ht1
  have hr := (SourceReferenceSigmaOne.reference_norm X t j hX hlog hj ht0).trans
    ((div_le_iff₀ (by linarith : 0< |t|)).mpr (by linarith : (450:ℝ)≤450*|t|))
  exact (norm_sub_le _ _).trans (add_le_add (atomPolynomial_bound S t) hr)

/-- Independent regularity of the unnormalized spectrum times its sharp window. -/
theorem unnormalized_square_integrable (X eta : ℝ) (j : ℕ × ℕ)
    (S : Finset SourceTriple) (hX : 2≤X) (hlog : 1000000≤Real.log X)
    (hj : j∈boxes (mesh X)) (he0 : 0≤eta) (he1 : eta<1) :
    Integrable (fun t => ‖MellinWindowFactor.factor 1 eta t*spectrum X j S t‖^2) := by
  let f := fun t => ‖MellinWindowFactor.factor 1 eta t*spectrum X j S t‖^2
  have hc : Continuous f := ((MellinWindowFactor.continuous_factor 1 eta
    (by norm_num) he1).mul (spectrum_continuous X j S (by linarith))).norm.pow 2
  have hw := SourceDyadicTail.weighted_integrable (spectrum X j S) 1 (atomMass S+450)
    (by norm_num) (spectrum_continuous X j S (by linarith)).measurable
    (fun t ht => spectrum_outside_bound X t j S hX hlog hj ht)
  have ht : IntegrableOn f (outside 1) := by
    apply (hw.const_mul 4).mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (outside_measurable 1)] with t ht
    have ht0 : t≠0 := by
      intro he
      have hh : 1< |t| := ht
      norm_num [he] at hh
    have h := pow_le_pow_left₀ (norm_nonneg _)
      (MellinWindowFactor.norm_le_frequency 1 eta t (by norm_num) he0 he1 ht0) 2
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg ‖spectrum X j S t‖)
    have he : (2/|t|)^2*‖spectrum X j S t‖^2=4*(‖spectrum X j S t‖^2/t^2) := by
      rw [div_pow,sq_abs]
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0≤f t from sq_nonneg _)]
    simpa only [f,norm_mul,mul_pow,he] using hm
  have hcover : Icc (-1:ℝ) 1∪outside 1=univ := by
    ext t
    simp only [mem_union,mem_Icc,outside,mem_setOf_eq,mem_univ,iff_true]
    by_cases hh : |t|≤1
    · exact Or.inl (abs_le.mp hh)
    · exact Or.inr (lt_of_not_ge hh)
  have hi : IntegrableOn f (Icc (-1:ℝ) 1∪outside 1) :=
    integrableOn_union.mpr ⟨hc.integrableOn_Icc,ht⟩
  rw [hcover] at hi
  simpa only [integrableOn_univ,f] using hi

theorem density_integrable (X Y : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hY : 0<Y) (hYX : Y≤X/2) : Integrable (density X Y j S) := by
  have hXp : 0<X := by linarith
  have he0 : 0<Y/X := div_pos hY hXp
  have he1 : Y/X<1 := (div_lt_one hXp).mpr (by linarith)
  have hi := (unnormalized_square_integrable X (Y/X) j S hX hlog hj he0.le he1).div_const ((Y/X)^2)
  have he (t : ℝ) : density X Y j S t =
      ‖MellinWindowFactor.factor 1 (Y/X) t*spectrum X j S t‖^2/(Y/X)^2 := by
    unfold density normalizedMultiplier
    rw [div_mul_eq_mul_div,norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [funext he]
  exact hi

theorem normalizedProfile_measurable (X Y : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple) :
    Measurable (normalizedProfile X Y j S) :=
  measurable_const.mul (selectedProfile_measurable X (1-Y/X) j S)

theorem normalizedProfile_integrable (X Y : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (hX : 0<X) (hY : 0<Y) (hYX : Y≤X/2) : Integrable (normalizedProfile X Y j S) := by
  have he0 : 0<Y/X := div_pos hY hX
  have he1 : Y/X≤1/2 := (div_le_iff₀ hX).mpr (by linarith)
  exact (selectedProfile_integrable X (1-Y/X) j S hX (by linarith)
    (by linarith)).const_mul _

theorem normalizedProfile_bound (X Y u : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (hX : 0<X) (hY : 0<Y) :
    ‖normalizedProfile X Y j S u‖ ≤ profileBound X j S/(Y/X) := by
  have he0 : 0<Y/X := div_pos hY hX
  rw [normalizedProfile,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos he0]
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left (selectedProfile_bound X (1-Y/X) u j S hX)
      (inv_nonneg.mpr he0.le)

theorem normalizedProfile_square_integrable (X Y : ℝ) (j : ℕ × ℕ)
    (S : Finset SourceTriple) (hX : 0<X) (hY : 0<Y) (hYX : Y≤X/2) :
    Integrable (fun u => ‖normalizedProfile X Y j S u‖^2) := by
  exact SourceAutocorrelation.square_integrable _ (profileBound X j S/(Y/X))
    (normalizedProfile_measurable X Y j S) (normalizedProfile_integrable X Y j S hX hY hYX)
    (div_nonneg (profileBound_nonneg X j S) (div_pos hY hX).le)
    (fun u => normalizedProfile_bound X Y u j S hX hY)

/-- Parseval for the SELECTED source and the ORIGINAL center.
The Fourier-square regularity premise of the inherited generic theorem is
constructed above, not accepted as an extra estimate. -/
theorem normalized_parseval (X Y : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hY : 0<Y) (hYX : Y≤X/2) :
    (∫ u : ℝ, ‖normalizedProfile X Y j S u‖^2) = energy X Y j S/(2*Real.pi) := by
  have hXp : 0<X := by linarith
  have haec : ∀ᵐ u : ℝ, ContinuousAt (normalizedProfile X Y j S) u := by
    filter_upwards [selectedProfile_ae_continuous X (1-Y/X) j S] with u hu
    exact continuousAt_const.mul hu
  have hFi : Integrable (fun t => ‖angular (normalizedProfile X Y j S) t‖^2) := by
    simp_rw [normalized_transform X Y _ j S hXp hY hYX]
    exact density_integrable X Y j S hX hlog hj hY hYX
  have hp := angular_parseval (normalizedProfile X Y j S) (profileBound X j S/(Y/X))
    (normalizedProfile_measurable X Y j S) (normalizedProfile_integrable X Y j S hXp hY hYX)
    (div_nonneg (profileBound_nonneg X j S) (div_pos hY hXp).le)
    (fun u => normalizedProfile_bound X Y u j S hXp hY) haec hFi
  simp_rw [normalized_transform X Y _ j S hXp hY hYX] at hp
  simpa only [energy,density,one_div,mul_comm,div_eq_mul_inv,one_mul] using hp

end Item1SelectedFourier


run_cmd do
  for target in [``Item1SelectedFourier.atomPolynomial_continuous,
    ``Item1SelectedFourier.atomPolynomial_bound,
    ``Item1SelectedFourier.atoms_transform,
    ``Item1SelectedFourier.fullReference_transform,
    ``Item1SelectedFourier.selected_transform,
    ``Item1SelectedFourier.normalized_transform,
    ``Item1SelectedFourier.spectrum_continuous,
    ``Item1SelectedFourier.spectrum_outside_bound,
    ``Item1SelectedFourier.unnormalized_square_integrable,
    ``Item1SelectedFourier.density_integrable,
    ``Item1SelectedFourier.normalizedProfile_measurable,
    ``Item1SelectedFourier.normalizedProfile_integrable,
    ``Item1SelectedFourier.normalizedProfile_bound,
    ``Item1SelectedFourier.normalizedProfile_square_integrable,
    ``Item1SelectedFourier.normalized_parseval] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"



