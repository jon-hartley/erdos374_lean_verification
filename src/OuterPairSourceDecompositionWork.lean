import OuterPairActualIntervalWork

/-! Exact finite decomposition of the original long-pair coefficient into
fixed-box outer-prime slices. Every source representation has one unique
index pair; no coefficient is duplicated or omitted. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace OuterPairSourceDecompositionWork
open OuterPairFixedBoxesWork OuterPairSourceIntervalWork
open SieveBoxTuples SieveWeightedCutoffs SieveGeometricGrid SieveBoxedFamily

def boxPairs (s : ℝ) : Finset (ℕ × ℕ) := boxIndices s ×ˢ boxIndices s

theorem source_weight_eq_box_sum (X s : ℝ) (P : Finset ℕ) (z : ℝ→ℝ)
    (hD : ∀p∈P,1<level X s/p) (hz : ∀p∈P,z p≤level X s/p) (hs : 0<s)
    (p d a b : ℕ) :
    (if (p,d,[a,b])∈LongPairCollectionWork.source X s P z then
      LongerTupleActualProfiles.originalWeight X s true (p,d,[a,b]) else 0) =
    ∑ ij∈boxPairs s,
      if fixedBoxSource X s P z d a b ij.1 ij.2 p then
        LongerTupleActualProfiles.originalWeight X s true (p,d,[a,b]) else 0 := by
  let w := LongerTupleActualProfiles.originalWeight X s true (p,d,[a,b])
  by_cases hsource : (p,d,[a,b])∈LongPairCollectionWork.source X s P z
  · obtain ⟨i,hi,j,hj,hfix⟩ :=
      (source_iff_fixedBoxSource X s P z hD hz hs p d a b).mp hsource
    have hmem : (i,j)∈boxPairs s := Finset.mem_product.mpr ⟨hi,hj⟩
    have hunique : ∀ij∈boxPairs s, ij≠(i,j) →
        (if fixedBoxSource X s P z d a b ij.1 ij.2 p then w else 0)=0 := by
      intro ij _ hne
      have hnot : ¬fixedBoxSource X s P z d a b ij.1 ij.2 p := by
        intro hf
        have hDp : 1<level X s/p := hD p hfix.1
        have hei := boxIndex_eq_of_inBox (level X s/p) s (a:ℝ) hDp hs
          ij.1 hf.2.2.2.2.1
        have hej := boxIndex_eq_of_inBox (level X s/p) s (b:ℝ) hDp hs
          ij.2 hf.2.2.2.2.2.1
        have hei0 := boxIndex_eq_of_inBox (level X s/p) s (a:ℝ) hDp hs
          i hfix.2.2.2.2.1
        have hej0 := boxIndex_eq_of_inBox (level X s/p) s (b:ℝ) hDp hs
          j hfix.2.2.2.2.2.1
        exact hne (Prod.ext (hei.symm.trans hei0) (hej.symm.trans hej0))
      simp [hnot]
    have hsum := Finset.sum_eq_single (i,j) hunique
      (fun hnot => False.elim (hnot hmem))
    simp only [if_pos hsource]
    simp only [hfix, ite_true] at hsum
    exact hsum.symm
  · have hzero : ∀ij∈boxPairs s,
        (if fixedBoxSource X s P z d a b ij.1 ij.2 p then w else 0)=0 := by
      intro ij hij
      have hnot : ¬fixedBoxSource X s P z d a b ij.1 ij.2 p := by
        intro hf
        have hm := Finset.mem_product.mp hij
        exact hsource ((source_iff_fixedBoxSource X s P z hD hz hs p d a b).mpr
          ⟨ij.1,hm.1,ij.2,hm.2,hf⟩)
      simp [hnot]
    simp only [if_neg hsource]
    exact (Finset.sum_eq_zero hzero).symm

run_cmd do
  for decl in [``source_weight_eq_box_sum] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPairSourceDecompositionWork
