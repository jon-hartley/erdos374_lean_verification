import SourceLiteralTransform
import Mathlib.Tactic

/-! UNCOMPILED PROOF-BODY DRAFT, 2026-10-02.
Select an arbitrary finite subset of the LITERAL ordered source tuples while
retaining the ORIGINAL full-Mangoldt reference. All reciprocals, endpoint
conventions, and product multiplicities are inherited. No arithmetic estimate,
small source mean, or Fourier/Parseval assertion is a hypothesis here.
The imported v7/v8/v9 drafts also still require elaboration and checking.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace Item1SelectedWindow
open PositiveSharpCounts CancellationTransferEndpoints CancellationTransferCenter
open PositiveInteriorModel SourceLiteralMoments SourceLiteralMass
open SourceLogWindow SourceWindowFourier SourceProfileConvolution
open SourceAngularConvolution SourceLiteralTransform

abbrev SourceTriple := ℕ × ℕ × ℕ

def primeTuple (a : SourceTriple) : Prop :=
  a.1.Prime ∧ a.2.1.Prime ∧ a.2.2.Prime

def primeTuples (X : ℝ) (j : ℕ × ℕ) : Finset SourceTriple :=
  by classical exact (sourceCoordinates X j).filter primeTuple

def badTuples (X : ℝ) (j : ℕ × ℕ) : Finset SourceTriple :=
  by classical exact (sourceCoordinates X j).filter (fun a => ¬primeTuple a)

def selectedCount (S : Finset SourceTriple) (x y : ℝ) : ℝ :=
  by classical exact ∑ a ∈ S.filter (inWindow x y), tripleWeight a

def atoms (S : Finset SourceTriple) (rho u : ℝ) : ℂ :=
  ∑ a ∈ S, atomCoefficient a * kernelC rho (u-Real.log (tripleProduct a))

def atomPolynomial (S : Finset SourceTriple) (t : ℝ) : ℂ :=
  ∑ a ∈ S, atomCoefficient a * phase t (Real.log (tripleProduct a))

/-- This reference is NEVER filtered by primality. -/
def fullReference (X : ℝ) (j : ℕ × ℕ) (rho u : ℝ) : ℂ :=
  ∑ p ∈ support X j 0, ∑ r ∈ support X j 1,
    pairCoefficient p r * referenceC rho (thirdScale X j/8) (4*thirdScale X j)
      (u-Real.log ((p:ℝ)*(r:ℝ)))

def selectedProfile (X : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (rho u : ℝ) : ℂ := atoms S rho u-fullReference X j rho u

def normalizedProfile (X Y : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (u : ℝ) : ℂ := ((Y/X:ℝ):ℂ)⁻¹ * selectedProfile X j S (1-Y/X) u

/-- The residual before division by the cell denominator. -/
def selectedResidual (X Y : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (x : ℝ) : ℝ :=
  selectedCount S x (x*Y/X)/(x*Y/X)-sourceMass j.1*sourceMass j.2

def atomMass (S : Finset SourceTriple) : ℝ := ∑ a ∈ S, ‖atomCoefficient a‖

def profileBound (X : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple) : ℝ :=
  atomMass S+∑ p ∈ support X j 0, ∑ r ∈ support X j 1, ‖pairCoefficient p r‖

theorem primeTuples_subset (X : ℝ) (j : ℕ × ℕ) :
    primeTuples X j ⊆ sourceCoordinates X j := by
  classical
  exact Finset.filter_subset _ _

theorem badTuples_subset (X : ℝ) (j : ℕ × ℕ) :
    badTuples X j ⊆ sourceCoordinates X j := by
  classical
  exact Finset.filter_subset _ _

/-- A generic finite partition identity, retaining every ordered tuple. -/
theorem tuple_partition {V : Type*} [AddCommMonoid V]
    (X : ℝ) (j : ℕ × ℕ) (f : SourceTriple → V) :
    (∑ a ∈ primeTuples X j, f a)+(∑ a ∈ badTuples X j, f a) =
      ∑ a ∈ sourceCoordinates X j, f a := by
  classical
  simp only [primeTuples,badTuples,Finset.sum_filter]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : primeTuple a <;> simp [ha]

theorem count_partition (X x y : ℝ) (j : ℕ × ℕ) :
    selectedCount (primeTuples X j) x y+selectedCount (badTuples X j) x y =
      sourceCount X j x y := by
  simpa only [selectedCount,sourceCount,Finset.sum_filter] using
    tuple_partition X j (fun a => if inWindow x y a then tripleWeight a else 0)

theorem selectedCount_nonneg (S : Finset SourceTriple) (x y : ℝ) :
    0 ≤ selectedCount S x y := by
  exact Finset.sum_nonneg (fun a _ => tripleWeight_nonneg a)

theorem atoms_integrable (S : Finset SourceTriple) (rho : ℝ) :
    Integrable (atoms S rho) := by
  exact integrable_finsetSum _ (fun a _ =>
    ((kernel_integrable rho).comp_sub_right _).const_mul _)

theorem atoms_measurable (S : Finset SourceTriple) (rho : ℝ) :
    Measurable (atoms S rho) := by
  apply Finset.measurable_fun_sum
  intro a _
  exact measurable_const.mul ((kernel_measurable rho).comp (measurable_id.sub_const _))

theorem atoms_bound (S : Finset SourceTriple) (rho u : ℝ) :
    ‖atoms S rho u‖ ≤ atomMass S := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_left (kernel_norm_le_one rho _)
    (norm_nonneg (atomCoefficient a))

theorem atoms_ae_continuous (S : Finset SourceTriple) (rho : ℝ) :
    ∀ᵐ u : ℝ, ContinuousAt (atoms S rho) u := by
  have hall : ∀ᵐ u : ℝ, ∀ a : SourceTriple,
      ContinuousAt (fun v => atomCoefficient a*kernelC rho (v-Real.log (tripleProduct a))) u := by
    apply ae_all_iff.mpr
    intro a
    filter_upwards [shifted_kernel_ae_continuous rho (Real.log (tripleProduct a))] with u hu
    exact continuousAt_const.mul hu
  filter_upwards [hall] with u hu
  exact tendsto_finsetSum _ (fun a _ => hu a)

theorem fullReference_integrable (X rho : ℝ) (j : ℕ × ℕ)
    (hX : 0<X) (hr0 : 0<rho) (hr1 : rho<1) :
    Integrable (fullReference X j rho) :=
  reference_sum_integrable X rho j hX hr0 hr1

theorem fullReference_continuous (X rho : ℝ) (j : ℕ × ℕ) :
    Continuous (fullReference X j rho) := by
  apply continuous_finset_sum
  intro p _
  apply continuous_finset_sum
  intro r _
  exact continuous_const.mul ((SourceProfileConvolution.reference_continuous rho _ _).comp
    (continuous_id.sub continuous_const))

theorem selectedProfile_integrable (X rho : ℝ) (j : ℕ × ℕ)
    (S : Finset SourceTriple) (hX : 0<X) (hr0 : 0<rho) (hr1 : rho<1) :
    Integrable (selectedProfile X j S rho) :=
  (atoms_integrable S rho).sub (fullReference_integrable X rho j hX hr0 hr1)

theorem selectedProfile_measurable (X rho : ℝ) (j : ℕ × ℕ)
    (S : Finset SourceTriple) : Measurable (selectedProfile X j S rho) :=
  (atoms_measurable S rho).sub (fullReference_continuous X rho j).measurable

theorem profileBound_nonneg (X : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple) :
    0 ≤ profileBound X j S := by unfold profileBound atomMass; positivity

theorem selectedProfile_bound (X rho u : ℝ) (j : ℕ × ℕ)
    (S : Finset SourceTriple) (hX : 0<X) :
    ‖selectedProfile X j S rho u‖ ≤ profileBound X j S := by
  have hL : 0<thirdScale X j := by unfold thirdScale PositiveInteriorModel.scale; positivity
  apply (norm_sub_le _ _).trans
  apply add_le_add (atoms_bound S rho u)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_left
    (reference_norm_le_one rho _ _ _ (by positivity)) (norm_nonneg (pairCoefficient p r))

theorem selectedProfile_ae_continuous (X rho : ℝ) (j : ℕ × ℕ)
    (S : Finset SourceTriple) : ∀ᵐ u : ℝ, ContinuousAt (selectedProfile X j S rho) u := by
  filter_upwards [atoms_ae_continuous S rho] with u hu
  exact hu.sub (fullReference_continuous X rho j).continuousAt

/-- The original strict-left, closed-right moving count, for any selected subset. -/
theorem atoms_log_identity (X x Y : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (hS : S ⊆ sourceCoordinates X j) (hx : 0<x) (hr : 0<1-Y/X) :
    atoms S (1-Y/X) (Real.log x) = ((selectedCount S x (x*Y/X)/x:ℝ):ℂ) := by
  have he : (1-Y/X)*x=x-x*Y/X := by ring
  unfold atoms selectedCount
  rw [Finset.sum_div]
  push_cast
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  have hid := atom_identity (1-Y/X) x (tripleProduct a) hr hx
    (triple_positive X j a (hS ha))
  have hidC := congrArg (fun z : ℝ => (z:ℂ)) hid
  simp only [kernelC,atomCoefficient]
  push_cast at hidC ⊢
  rw [show (tripleWeight a:ℂ)/(tripleProduct a:ℂ)*
      (SourceLogWindow.kernel (1-Y/X) (Real.log x-Real.log (tripleProduct a)):ℂ) =
      (tripleWeight a:ℂ)*((SourceLogWindow.kernel (1-Y/X)
        (Real.log x-Real.log (tripleProduct a)):ℂ)/(tripleProduct a:ℂ)) by ring,
    hidC]
  rw [he]
  dsimp [inWindow]
  split_ifs <;> norm_num <;> ring

theorem fullReference_eq_original (X rho u : ℝ) (j : ℕ × ℕ) :
    fullReference X j rho u = (referenceProfile X j rho u:ℂ) := by
  unfold fullReference referenceProfile pairCoefficient referenceC
  push_cast
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Exact width normalization; eta=Y/X, and no cell denominator has entered yet. -/
theorem normalizedProfile_log (X x Y : ℝ) (j : ℕ × ℕ) (S : Finset SourceTriple)
    (hS : S ⊆ sourceCoordinates X j) (hX : 0<X)
    (hx : x∈Icc X (2*X)) (hY : 0<Y) (hYX : Y≤X/2) :
    normalizedProfile X Y j S (Real.log x) = (selectedResidual X Y j S x:ℂ) := by
  have hxp : 0<x := hX.trans_le hx.1
  have hr : 0<1-Y/X := by
    have hh := (div_le_iff₀ hX).mpr (show Y≤(1/2)*X by linarith)
    linarith
  rw [normalizedProfile,selectedProfile,atoms_log_identity X x Y j S hS hxp hr,
    fullReference_eq_original,reference_eq_center X x Y j hX hx hY.le hYX]
  unfold selectedResidual
  push_cast
  have hxc : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hxp.ne'
  have hXc : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hYc : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  field_simp [hxc,hXc,hYc] <;> ring

end Item1SelectedWindow


run_cmd do
  for target in [``Item1SelectedWindow.primeTuples_subset,
    ``Item1SelectedWindow.badTuples_subset,
    ``Item1SelectedWindow.tuple_partition,
    ``Item1SelectedWindow.count_partition,
    ``Item1SelectedWindow.selectedCount_nonneg,
    ``Item1SelectedWindow.atoms_integrable,
    ``Item1SelectedWindow.atoms_measurable,
    ``Item1SelectedWindow.atoms_bound,
    ``Item1SelectedWindow.atoms_ae_continuous,
    ``Item1SelectedWindow.fullReference_integrable,
    ``Item1SelectedWindow.fullReference_continuous,
    ``Item1SelectedWindow.selectedProfile_integrable,
    ``Item1SelectedWindow.selectedProfile_measurable,
    ``Item1SelectedWindow.profileBound_nonneg,
    ``Item1SelectedWindow.selectedProfile_bound,
    ``Item1SelectedWindow.selectedProfile_ae_continuous,
    ``Item1SelectedWindow.atoms_log_identity,
    ``Item1SelectedWindow.fullReference_eq_original,
    ``Item1SelectedWindow.normalizedProfile_log] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"



