import OuterSmoothErrorMeanWork

/-! Exact assembly of the rectangular sharp and continuous source masks.
The continuous replacement retains the signed divisor atom and the full
centered floor kernel. Its error includes exterior representations. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace OuterSmoothCoreWork
open LongerTupleEncoding LongerTupleActualProfiles OuterSourceReindexWork
open LongPairCloseDistinctMeanWork OuterBoundaryExtensionWork
open OuterSmoothErrorSupportWork OuterSmoothStepWork OuterBufferedSourceWork
open OuterSeparatedLogMaskWork OuterSeparatedCoreIntervalWork OuterBufferedLogMaskWork
open OuterDivisorIntervalWork OuterPairSourceDecompositionWork UpperAfter545Remaining

def atomMultiplier (X s : ℝ) (i j : ℕ) (r : Representation) : ℝ :=
  (divisorAtom X s (drop r).1 r.1).re *
    (if tupleMask X s (drop r).2.1 (drop r).2.2 i j then 1 else 0)

def sharpBox (X s L R : ℝ) (i j : ℕ) : ℝ :=
  ∑r∈ambient X,atomMultiplier X s i j r *
    sharpCuts (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j)*floorKernel L R (index r)

def smoothBox (X s L R : ℝ) (i j : ℕ) : ℝ :=
  ∑r∈ambient X,atomMultiplier X s i j r *
    smoothCuts (width X) (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j)*floorKernel L R (index r)

def smoothRemainder (X s L R : ℝ) : ℝ := ∑ij∈boxPairs s,smoothBox X s L R ij.1 ij.2

theorem atomMultiplier_abs_le (X s : ℝ) (i j : ℕ) (r : Representation) :
    |atomMultiplier X s i j r|≤1 := by
  have hh := (Complex.abs_re_le_norm (divisorAtom X s (drop r).1 r.1)).trans
    (divisorAtom_norm_le X s (drop r).1 r.1)
  unfold atomMultiplier
  split_ifs
  · simpa using hh
  · simp

theorem source_subset_ambient (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) : separatedSource X s⊆ambient X := by
  intro r hr
  have hd := separated_source_data X s r hr
  have hu := source_slices_subset X s hX hs hs1 hlog (Finset.mem_image.mpr ⟨r,hr,rfl⟩)
  exact Finset.mem_biUnion.mpr ⟨drop r,hu,Finset.mem_image.mpr ⟨r.1,hd.2,rebuild_drop r hd.1⟩⟩

theorem sharpCoefficient_eq (X s : ℝ) (hX : 2≤X) (hs : 0<s)
    (r : Representation) (hr : r∈ambient X) (i j : ℕ) :
    (if coreBoxSource X s (drop r).1 (drop r).2.1 (drop r).2.2 i j r.1 then
      originalWeight X s true r else 0).re =
    atomMultiplier X s i j r*sharpCuts (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) := by
  have hd := ambient_data X hX r hr
  have hpP : r.1∈PositiveSharpBoxedCount.largePrimes X := by
    obtain ⟨u,_,hr'⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hr'
    simpa only [←he,rebuild] using hp
  have he := congrArg Complex.re (coreBox_weight_eq_atoms X s r.1 (drop r).1
    (drop r).2.1 (drop r).2.2 i j (by linarith) hpP hd.2.2.1
    hd.2.2.2.2.1 hd.2.2.2.2.2.1 hd.2.2.2.2.2.2)
  have hrb : (r.1,(drop r).1,[(drop r).2.1,(drop r).2.2])=r := rebuild_drop r hd.1
  have hz := (logMask_iff_thresholdCuts X s (drop r) i j r.1 hs).symm
  simpa [hrb,atomMultiplier,sharpCuts,hz,Complex.mul_re,apply_ite] using he

theorem source_coefficient_eq (X s : ℝ) (hX : 2≤X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (r : Representation) (hr : r∈ambient X) :
    (if r∈separatedSource X s then (originalWeight X s true r).re else 0) =
      ∑ij∈boxPairs s,atomMultiplier X s ij.1 ij.2 r*
        sharpCuts (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) ij.1 ij.2) := by
  have hd := ambient_data X hX r hr
  have hrb : (r.1,(drop r).1,[(drop r).2.1,(drop r).2.2])=r := rebuild_drop r hd.1
  have he := congrArg Complex.re (separated_weight_eq_box_sum X s (by linarith) hs hs1 hlog
    r.1 (drop r).1 (drop r).2.1 (drop r).2.2)
  calc
    _ = ∑ij∈boxPairs s,
        (if coreBoxSource X s (drop r).1 (drop r).2.1 (drop r).2.2 ij.1 ij.2 r.1 then
          originalWeight X s true r else 0).re := by
      simpa only [hrb,Complex.re_sum,apply_ite,Complex.zero_re] using he
    _ = _ := Finset.sum_congr rfl (fun ij _ => sharpCoefficient_eq X s hX hs r hr ij.1 ij.2)

theorem separated_eq_sharpBoxes (X s L R : ℝ) (hX : 2≤X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) :
    separatedRemainder X s L R = ∑ij∈boxPairs s,sharpBox X s L R ij.1 ij.2 := by
  have hsub := source_subset_ambient X s (by linarith) hs hs1 hlog
  have hf : (ambient X).filter (fun r => r∈separatedSource X s)=separatedSource X s := by
    ext r
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hsub h,h⟩⟩
  calc
    _ = ∑r∈ambient X,(if r∈separatedSource X s then
        (originalWeight X s true r).re else 0)*floorKernel L R (index r) := by
      simp only [separatedRemainder,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,mul_zero,sub_zero]
      conv_lhs => rw [←hf,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> simp
    _ = ∑r∈ambient X,(∑ij∈boxPairs s,atomMultiplier X s ij.1 ij.2 r*
        sharpCuts (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) ij.1 ij.2))*floorKernel L R (index r) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [source_coefficient_eq X s hX hs hs1 hlog r hr]
    _ = _ := by simp_rw [Finset.sum_mul]; exact Finset.sum_comm

theorem sharp_sub_smoothBox (X s L R : ℝ) (i j : ℕ) :
    sharpBox X s L R i j-smoothBox X s L R i j =
      ∑r∈ambient X,(atomMultiplier X s i j r*maskError X s (drop r) i j r.1)*
        floorKernel L R (index r) := by
  simp only [sharpBox,smoothBox,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  unfold maskError
  ring

theorem remainder_difference (X s L R : ℝ) (hX : 2≤X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) :
    separatedRemainder X s L R-smoothRemainder X s L R =
      ∑ij∈boxPairs s,∑r∈ambient X,
        (atomMultiplier X s ij.1 ij.2 r*maskError X s (drop r) ij.1 ij.2 r.1)*
          floorKernel L R (index r) := by
  rw [separated_eq_sharpBoxes X s L R hX hs hs1 hlog]
  simp only [smoothRemainder,←Finset.sum_sub_distrib,sharp_sub_smoothBox]

run_cmd do
  for decl in [``atomMultiplier_abs_le, ``source_subset_ambient,
      ``sharpCoefficient_eq, ``source_coefficient_eq, ``separated_eq_sharpBoxes,
      ``sharp_sub_smoothBox, ``remainder_difference] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSmoothCoreWork
