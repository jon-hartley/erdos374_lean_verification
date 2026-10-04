import OuterPairOrderWork

/-! Exact finite-box expansion of the actual outer long-pair source.
The box indices run over a set depending only on s. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace OuterPairFixedBoxesWork
open SieveGeometricGrid SieveBoxTuples SieveBoxedFamily SieveWeightedCutoffs
open LongerTupleEncoding

def boxIndices (s : ℝ) : Finset ℕ := Finset.range (cutoff s+1)

theorem mem_source_iff_fixed_boxes (X s : ℝ) (P : Finset ℕ) (z : ℝ→ℝ)
    (hD : ∀p∈P,1<level X s/p) (hz : ∀p∈P,z p≤level X s/p) (hs : 0<s)
    (p d a b : ℕ) :
    (p,d,[a,b])∈LongPairCollectionWork.source X s P z ↔
      p∈P ∧ d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s ∧
      a∈pool (level X s/p) s (z p) ∧
      b∈pool (level X s/p) s (z p) ∧
      (∃ i : ℕ, i∈boxIndices s ∧ ∃ j : ℕ, j∈boxIndices s ∧
        InBox (level X s/p) s (a:ℝ) i ∧
        InBox (level X s/p) s (b:ℝ) j ∧ j ≤ i ∧ 3*exponent s i < 1) ∧
      LongerTupleSector.allLong X [a,b] ∧
      X^(109/200:ℝ)<(index (p,d,[a,b]):ℝ) := by
  rw [OuterPairBoxGateWork.mem_long_pair_source X s P z hD hs p d a b]
  constructor
  · rintro ⟨hp,hd,ha,hb,ho,hg,hl,hm⟩
    obtain ⟨_,haz,hal⟩ := (mem_pool _ _ _ a).mp ha
    obtain ⟨_,hbz,hbl⟩ := (mem_pool _ _ _ b).mp hb
    let D := level X s/p
    have hia := boxIndex_spec D s (a:ℝ) (hD p hp) hs hal (haz.trans_le (hz p hp))
    have hjb := boxIndex_spec D s (b:ℝ) (hD p hp) hs hbl (hbz.trans_le (hz p hp))
    have hi : boxIndex D s (a:ℝ)∈boxIndices s := by
      simp only [boxIndices,Finset.mem_range,Nat.lt_succ_iff]
      exact boxIndex_le_cutoff D s (a:ℝ) (hD p hp) hs hal (haz.trans_le (hz p hp))
    have hj : boxIndex D s (b:ℝ)∈boxIndices s := by
      simp only [boxIndices,Finset.mem_range,Nat.lt_succ_iff]
      exact boxIndex_le_cutoff D s (b:ℝ) (hD p hp) hs hbl (hbz.trans_le (hz p hp))
    exact ⟨hp,hd,ha,hb,⟨_,hi,_,hj,hia,hjb,ho,hg⟩,hl,hm⟩
  · rintro ⟨hp,hd,ha,hb,⟨i,_,j,_,hia,hjb,hji,hg⟩,hl,hm⟩
    have hei := boxIndex_eq_of_inBox (level X s/p) s (a:ℝ) (hD p hp) hs i hia
    have hej := boxIndex_eq_of_inBox (level X s/p) s (b:ℝ) (hD p hp) hs j hjb
    subst i
    subst j
    exact ⟨hp,hd,ha,hb,hji,hg,hl,hm⟩

run_cmd do
  for decl in [``mem_source_iff_fixed_boxes] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPairFixedBoxesWork
