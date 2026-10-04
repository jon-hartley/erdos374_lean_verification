import OuterNineCutTruncationWork
import OuterAmbientSizeWork
import OuterSmoothApproximationWork

/-! The finite-frequency source replacement retains the actual signed
weights, all ambient representations, and the centered floor kernel. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterTruncatedCoreWork
open OuterNineCutTruncationWork OuterSmoothCoreWork OuterSmoothErrorSupportWork
open OuterSmoothStepWork OuterBufferedSourceWork OuterSourceReindexWork
open OuterPairSourceDecompositionWork LongerTupleEncoding UpperAfter545Remaining

def truncatedBox (X s L R : ℝ) (i j : ℕ) : ℝ :=
  ∑r∈ambient X, atomMultiplier X s i j r*(truncatedCuts X s (X^4) r i j).re*
    floorKernel L R (index r)
def truncatedRemainder (X s L R : ℝ) : ℝ :=
  ∑ij∈boxPairs s, truncatedBox X s L R ij.1 ij.2

def coefficientError (X s : ℝ) (i j : ℕ) (r : Representation) : ℝ :=
  atomMultiplier X s i j r*(smoothCuts (width X) (Real.log (r.1:ℝ))
    (cutoffLogs X s (drop r) i j)-(truncatedCuts X s (X^4) r i j).re)

theorem coefficientError_bound (X s : ℝ) (hX : 2 ≤ X) (r : Representation)
    (hr : r ∈ ambient X) (i j : ℕ) : |coefficientError X s i j r| ≤ 4088/X^3 := by
  have he := source_nine_polynomial_error X s hX r hr i j
  have hr' := Complex.abs_re_le_norm
    ((smoothCuts (width X) (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j):ℂ)-
      truncatedCuts X s (X^4) r i j)
  simp only [Complex.sub_re,Complex.ofReal_re] at hr'
  have hh := hr'.trans he
  have hcap : 4088/(Real.pi*X^3) ≤ 4088/X^3 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [Real.pi_gt_three,show 0 < X^3 by positivity]
  rw [coefficientError,abs_mul]
  calc
    _ ≤ 1*(4088/X^3) := mul_le_mul (atomMultiplier_abs_le X s i j r)
      (hh.trans hcap) (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem box_difference (X s L R : ℝ) (i j : ℕ) :
    smoothBox X s L R i j-truncatedBox X s L R i j =
      ∑r∈ambient X,coefficientError X s i j r*floorKernel L R (index r) := by
  rw [smoothBox,truncatedBox,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  unfold coefficientError
  ring

theorem truncated_moving_integrable (X s Y : ℝ) :
    IntegrableOn (fun x => truncatedRemainder X s (x-x*(Y/X)) x) (Icc X (2*X)) := by
  unfold truncatedRemainder truncatedBox
  exact integrable_finsetSum (boxPairs s) (fun ij _ =>
    integrable_finsetSum (ambient X) (fun r _ =>
      (SparseFloorMeanWork.kernel_integrable (index r) X Y).const_mul _))

run_cmd do
  for decl in [``coefficientError_bound, ``box_difference, ``truncated_moving_integrable] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterTruncatedCoreWork
