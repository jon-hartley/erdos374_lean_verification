import OuterPairBoxMonotoneWork

/-! The remaining pair-order test is automatic for descending actual primes.
Ascending pairs survive only when both primes occupy the same grid box. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace OuterPairOrderWork
open SieveBoxedFamily SieveBoxTuples SieveGeometricGrid SieveWeightedCutoffs
open LongerTupleEncoding

theorem grid_order_iff (D s z : ℝ) (hD : 1<D) (hs : 0<s) (hz : z≤D)
    (a b : ℕ) (ha : a∈pool D s z) (hb : b∈pool D s z) :
    boxIndex D s (a:ℝ)≥boxIndex D s (b:ℝ) ↔
      b≤a ∨ boxIndex D s (a:ℝ)=boxIndex D s (b:ℝ) := by
  obtain ⟨_,haz,hal⟩ := (mem_pool _ _ _ a).mp ha
  obtain ⟨_,hbz,hbl⟩ := (mem_pool _ _ _ b).mp hb
  have haBox := boxIndex_spec D s (a:ℝ) hD hs hal (haz.trans_le hz)
  have hbBox := boxIndex_spec D s (b:ℝ) hD hs hbl (hbz.trans_le hz)
  constructor
  · intro h
    by_cases hba : b≤a
    · exact Or.inl hba
    · right
      have hab : (a:ℝ)≤b := by exact_mod_cast (show a≤b by omega)
      have hle := index_le_of_value_le D s (a:ℝ) (b:ℝ) hD hs _ _ haBox hbBox hab
      omega
  · rintro (hba | he)
    · apply index_le_of_value_le D s (b:ℝ) (a:ℝ) hD hs _ _ hbBox haBox
      exact_mod_cast hba
    · omega

/-- Literal source membership, with the order test reduced to an actual
prime order or an equal-box collision. -/
theorem mem_source_order_or_collision (X s : ℝ) (P : Finset ℕ) (z : ℝ→ℝ)
    (hD : ∀p∈P,1<level X s/p) (hz : ∀p∈P,z p≤level X s/p) (hs : 0<s)
    (p d a b : ℕ) :
    (p,d,[a,b])∈LongPairCollectionWork.source X s P z ↔
      p∈P ∧ d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s ∧
      a∈pool (level X s/p) s (z p) ∧
      b∈pool (level X s/p) s (z p) ∧
      (b≤a ∨ boxIndex (level X s/p) s (a:ℝ)=boxIndex (level X s/p) s (b:ℝ)) ∧
      3*exponent s (boxIndex (level X s/p) s (a:ℝ))<1 ∧
      LongerTupleSector.allLong X [a,b] ∧
      X^(109/200:ℝ)<(index (p,d,[a,b]):ℝ) := by
  rw [OuterPairBoxGateWork.mem_long_pair_source X s P z hD hs p d a b]
  constructor
  · rintro ⟨hp,hd,ha,hb,ho,hg,hl,hm⟩
    exact ⟨hp,hd,ha,hb,(grid_order_iff _ _ _ (hD p hp) hs (hz p hp) a b ha hb).mp ho,hg,hl,hm⟩
  · rintro ⟨hp,hd,ha,hb,ho,hg,hl,hm⟩
    exact ⟨hp,hd,ha,hb,(grid_order_iff _ _ _ (hD p hp) hs (hz p hp) a b ha hb).mpr ho,hg,hl,hm⟩

run_cmd do
  for decl in [``grid_order_iff, ``mem_source_order_or_collision] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPairOrderWork
