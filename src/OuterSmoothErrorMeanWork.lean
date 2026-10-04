import OuterSmoothErrorSupportWork

/-! Absolute-mean control for the continuous mask error on the enlarged
ambient family. The theorem includes all newly introduced exterior terms
and is uniform in signed unit multipliers. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable
open Filter MeasureTheory Set
open scoped BigOperators

namespace OuterSmoothErrorMeanWork
open LongerTupleEncoding OuterSourceReindexWork OuterBufferedSourceWork
open OuterPairSourceDecompositionWork OuterSmoothErrorSupportWork
open OuterBoundaryExtensionWork UpperAfter545Remaining

theorem sum_errorSupport_eq (X s : ℝ) (i j : ℕ) (w : Representation→ℝ) (L R : ℝ) :
    (∑r∈errorSupport X s i j,
      (w r*maskError X s (drop r) i j r.1)*floorKernel L R (index r)) =
    ∑r∈ambient X,(w r*maskError X s (drop r) i j r.1)*floorKernel L R (index r) := by
  simp only [errorSupport,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hh : maskError X s (drop r) i j r.1=0 <;> simp [hh]

theorem eventually_mask_error_mean (s : ℝ) :
    ∀ᶠ X : ℝ in atTop, 2≤X ∧ 1000≤Real.log X ∧
      ∀ij∈boxPairs s, ∀w : Representation→ℝ, (∀r∈ambient X,|w r|≤1) →
      ∀Y : ℝ, 0≤Y → Y≤X/2 →
        (1/X)*(∫x in Icc X (2*X),
          |∑r∈ambient X,(w r*maskError X s (drop r) ij.1 ij.2 r.1)*
            floorKernel (x-x*(Y/X)) x (index r)|) ≤ Y*X^(-19/100:ℝ) := by
  filter_upwards [eventually_extended_boundary_absolute ((boxPairs s).card*27),
    eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000:ℝ))] with X hm hX hlog
  refine ⟨hX,hlog,?_⟩
  intro ij hij w hw Y hY hYX
  have hh := hm.2 (boundaryPrimes X s) (boundaryPrimes_card X s)
    (errorSupport X s ij.1 ij.2) (errorSupport_subset X s hX ij hij)
    (errorSupport_index X s hX hlog ij.1 ij.2)
    (fun r => w r*maskError X s (drop r) ij.1 ij.2 r.1)
    (by intro r hr
        rw [abs_mul]
        calc
          _ ≤ 1*1 := mul_le_mul (hw r (Finset.mem_filter.mp hr).1)
            (maskError_abs_le X s (drop r) ij.1 ij.2 r.1) (abs_nonneg _) (by norm_num)
          _ = 1 := by norm_num) Y hY hYX
  simpa only [sum_errorSupport_eq] using hh

run_cmd do
  for decl in [``sum_errorSupport_eq, ``eventually_mask_error_mean] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSmoothErrorMeanWork
