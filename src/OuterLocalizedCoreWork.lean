import OuterTruncatedMeanWork
import OuterActiveDyadicWork

/-! Restrict the Fourier replacement to dyadic blocks meeting the active
smooth source. The full truncation mean bound is preserved. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterLocalizedCoreWork
open OuterActiveDyadicWork OuterTruncatedCoreWork OuterTruncatedMeanWork
open OuterSmoothCoreWork OuterNineCutTruncationWork OuterSmoothErrorSupportWork
open OuterPairSourceDecompositionWork LongerTupleEncoding UpperAfter545Remaining
open LongerTupleHigherMeanWork OuterAmbientSizeWork

def localizedBox (X s L R : ℝ) (i j : ℕ) : ℝ :=
  ∑r∈localizedSource X s i j, atomMultiplier X s i j r*(truncatedCuts X s (X^4) r i j).re*
    floorKernel L R (index r)
def localizedRemainder (X s L R : ℝ) : ℝ :=
  ∑ij∈boxPairs s, localizedBox X s L R ij.1 ij.2

theorem localized_card_le (X s : ℝ) (hX : 2 ≤ X) (i j : ℕ) :
    ((localizedSource X s i j).card:ℝ) ≤ X^2 := by
  exact (by exact_mod_cast Finset.card_le_card (localized_subset X s i j) :
    ((localizedSource X s i j).card:ℝ) ≤ (ambient X).card).trans (ambient_card_le X hX)

theorem localized_box_difference (X s L R : ℝ) (i j : ℕ) :
    smoothBox X s L R i j-localizedBox X s L R i j =
      ∑r∈localizedSource X s i j,coefficientError X s i j r*floorKernel L R (index r) := by
  rw [smoothBox_localized,localizedBox,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  unfold coefficientError
  ring

theorem localized_moving_integrable (X s Y : ℝ) :
    IntegrableOn (fun x => localizedRemainder X s (x-x*(Y/X)) x) (Icc X (2*X)) := by
  unfold localizedRemainder localizedBox
  exact integrable_finsetSum (boxPairs s) (fun ij _ =>
    integrable_finsetSum (localizedSource X s ij.1 ij.2) (fun r _ =>
      (SparseFloorMeanWork.kernel_integrable (index r) X Y).const_mul _))

theorem localized_box_error_mean (X s Y : ℝ) (hX : 2 ≤ X) (hY : 0 ≤ Y)
    (hYX : Y ≤ X/2) (i j : ℕ) :
    (1/X)*(∫x in Icc X (2*X),
      |smoothBox X s (x-x*(Y/X)) x i j-localizedBox X s (x-x*(Y/X)) x i j|) ≤ 24528*Y/X := by
  simp_rw [localized_box_difference]
  apply (absolute_sum_mean_le (localizedSource X s i j)
    (fun r x => coefficientError X s i j r*floorKernel (x-x*(Y/X)) x (index r)) X
    (by linarith) (fun r _ => (SparseFloorMeanWork.kernel_integrable (index r) X Y).const_mul _)).trans
  calc
    _ ≤ ∑_r∈localizedSource X s i j,(4088/X^3)*(6*Y) := Finset.sum_le_sum (fun r hr =>
      weighted_kernel_mean X Y (4088/X^3) _ (index r) hX hY hYX (by positivity)
        (coefficientError_bound X s hX r (localized_subset X s i j hr) i j)
        (ambient_index_pos X hX r (localized_subset X s i j hr)))
    _ = ((localizedSource X s i j).card:ℝ)*((4088/X^3)*(6*Y)) := by simp
    _ ≤ X^2*((4088/X^3)*(6*Y)) := mul_le_mul_of_nonneg_right (localized_card_le X s hX i j) (by positivity)
    _ = _ := by field_simp; ring

theorem localized_full_error_mean (X s Y : ℝ) (hX : 2 ≤ X) (hY : 0 ≤ Y) (hYX : Y ≤ X/2) :
    (1/X)*(∫x in Icc X (2*X),
      |smoothRemainder X s (x-x*(Y/X)) x-localizedRemainder X s (x-x*(Y/X)) x|) ≤
        (24528*(boxPairs s).card)*Y/X := by
  have he (x : ℝ) : smoothRemainder X s (x-x*(Y/X)) x-localizedRemainder X s (x-x*(Y/X)) x =
      ∑ij∈boxPairs s, (smoothBox X s (x-x*(Y/X)) x ij.1 ij.2-
        localizedBox X s (x-x*(Y/X)) x ij.1 ij.2) := by
    simp only [smoothRemainder,localizedRemainder,Finset.sum_sub_distrib]
  simp_rw [he]
  have hi (ij : ℕ×ℕ) : IntegrableOn (fun x =>
      smoothBox X s (x-x*(Y/X)) x ij.1 ij.2-
      localizedBox X s (x-x*(Y/X)) x ij.1 ij.2) (Icc X (2*X)) := by
    simp_rw [localized_box_difference]
    exact integrable_finsetSum (localizedSource X s ij.1 ij.2) (fun r _ =>
      (SparseFloorMeanWork.kernel_integrable (index r) X Y).const_mul _)
  apply (absolute_sum_mean_le (boxPairs s)
    (fun ij x => smoothBox X s (x-x*(Y/X)) x ij.1 ij.2-
      localizedBox X s (x-x*(Y/X)) x ij.1 ij.2) X (by linarith) (fun ij _ => hi ij)).trans
  calc
    _ ≤ ∑_ij∈boxPairs s,24528*Y/X := Finset.sum_le_sum (fun ij _ => localized_box_error_mean X s Y hX hY hYX ij.1 ij.2)
    _ = _ := by simp; ring

run_cmd do
  for decl in [``localized_card_le, ``localized_box_difference, ``localized_moving_integrable,
      ``localized_box_error_mean, ``localized_full_error_mean] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterLocalizedCoreWork
