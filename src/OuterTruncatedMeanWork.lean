import OuterTruncatedCoreWork

/-! Absolute moving-mean error for the entire finite-frequency replacement,
with the signed divisor coefficients and centered kernels retained. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterTruncatedMeanWork
open OuterTruncatedCoreWork OuterAmbientSizeWork OuterSmoothCoreWork
open OuterSmoothErrorSupportWork OuterPairSourceDecompositionWork
open LongerTupleEncoding UpperAfter545Remaining LongerTupleHigherMeanWork

theorem weighted_kernel_mean (X Y E w : ℝ) (m : ℕ) (hX : 2 ≤ X)
    (hY : 0 ≤ Y) (hYX : Y ≤ X/2) (hE : 0 ≤ E) (hw : |w| ≤ E) (hm : 0 < m) :
    (1/X)*(∫x in Icc X (2*X), |w*floorKernel (x-x*(Y/X)) x m|) ≤ E*(6*Y) := by
  have hXp : 0 < X := by linarith
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hb := SparseFloorMeanWork.single_absolute_mean m X Y hXp hY hYX hm
  have h1 : 2*Y/X ≤ 2*Y := (div_le_iff₀ hXp).mpr (by nlinarith)
  have h2 : 4*Y/(m:ℝ) ≤ 4*Y := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hb' : (1/X)*(∫x in Icc X (2*X),|floorKernel (x-x*(Y/X)) x m|) ≤ 6*Y := by linarith
  simp_rw [abs_mul]
  rw [integral_const_mul]
  calc
    _ = |w| * ((1/X)*(∫x in Icc X (2*X),|floorKernel (x-x*(Y/X)) x m|)) := by ring
    _ ≤ E*(6*Y) := mul_le_mul hw hb' (by positivity) hE

theorem box_error_mean (X s Y : ℝ) (hX : 2 ≤ X) (hY : 0 ≤ Y)
    (hYX : Y ≤ X/2) (i j : ℕ) :
    (1/X)*(∫x in Icc X (2*X),
      |smoothBox X s (x-x*(Y/X)) x i j-truncatedBox X s (x-x*(Y/X)) x i j|) ≤
        24528*Y/X := by
  simp_rw [box_difference]
  apply (absolute_sum_mean_le (ambient X)
    (fun r x => coefficientError X s i j r*floorKernel (x-x*(Y/X)) x (index r)) X
    (by linarith) (fun r _ => (SparseFloorMeanWork.kernel_integrable (index r) X Y).const_mul _)).trans
  calc
    _ ≤ ∑_r∈ambient X,(4088/X^3)*(6*Y) := Finset.sum_le_sum (fun r hr =>
      weighted_kernel_mean X Y (4088/X^3) _ (index r) hX hY hYX (by positivity)
        (coefficientError_bound X s hX r hr i j) (ambient_index_pos X hX r hr))
    _ = ((ambient X).card:ℝ)*((4088/X^3)*(6*Y)) := by simp
    _ ≤ X^2*((4088/X^3)*(6*Y)) := mul_le_mul_of_nonneg_right (ambient_card_le X hX) (by positivity)
    _ = _ := by field_simp; ring

theorem full_error_mean (X s Y : ℝ) (hX : 2 ≤ X) (hY : 0 ≤ Y) (hYX : Y ≤ X/2) :
    (1/X)*(∫x in Icc X (2*X),
      |smoothRemainder X s (x-x*(Y/X)) x-truncatedRemainder X s (x-x*(Y/X)) x|) ≤
        (24528*(boxPairs s).card)*Y/X := by
  have he (x : ℝ) : smoothRemainder X s (x-x*(Y/X)) x-truncatedRemainder X s (x-x*(Y/X)) x =
      ∑ij∈boxPairs s, (smoothBox X s (x-x*(Y/X)) x ij.1 ij.2-
        truncatedBox X s (x-x*(Y/X)) x ij.1 ij.2) := by
    simp only [smoothRemainder,truncatedRemainder,Finset.sum_sub_distrib]
  simp_rw [he]
  have hi (ij : ℕ×ℕ) : IntegrableOn (fun x =>
      smoothBox X s (x-x*(Y/X)) x ij.1 ij.2-
      truncatedBox X s (x-x*(Y/X)) x ij.1 ij.2) (Icc X (2*X)) := by
    simp_rw [box_difference]
    exact integrable_finsetSum (ambient X) (fun r _ =>
      (SparseFloorMeanWork.kernel_integrable (index r) X Y).const_mul _)
  apply (absolute_sum_mean_le (boxPairs s)
    (fun ij x => smoothBox X s (x-x*(Y/X)) x ij.1 ij.2-
      truncatedBox X s (x-x*(Y/X)) x ij.1 ij.2) X (by linarith) (fun ij _ => hi ij)).trans
  calc
    _ ≤ ∑_ij∈boxPairs s,24528*Y/X := Finset.sum_le_sum (fun ij _ => box_error_mean X s Y hX hY hYX ij.1 ij.2)
    _ = _ := by simp; ring

run_cmd do
  for decl in [``weighted_kernel_mean, ``box_error_mean, ``full_error_mean] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterTruncatedMeanWork
