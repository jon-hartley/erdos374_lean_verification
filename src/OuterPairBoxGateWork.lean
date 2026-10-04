import LongPairSeparatedCoreWork

/-! Expose the literal length-two outer boxing test as a grid-order condition
and one first-coordinate gate. All pool and source restrictions are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace OuterPairBoxGateWork
open SieveBoxedFamily SieveUpperBoxFamily SieveGeometricGrid SieveBoxTuples
open LongerTupleEncoding LongerTupleActualProfiles SieveWeightedCutoffs

/-- The outer two-prime boxing predicate has exactly one prefix gate. -/
theorem outerTest_pair (D s : ℝ) (a b : ℕ) :
    SieveUpperBoxFamily.outerTest D s [a,b] ↔
      boxIndex D s (a:ℝ) ≥ boxIndex D s (b:ℝ) ∧
      (coordinate D s a)^3<D := by
  simp [SieveUpperBoxFamily.outerTest,SieveBoxedFamily.indices,
    SieveBoxedFamily.scales,SieveBoxPrefix.accepts]

/-- For D>1 the first-coordinate gate is an index threshold. -/
theorem outerTest_pair_index (D s : ℝ) (hD : 1<D) (a b : ℕ) :
    SieveUpperBoxFamily.outerTest D s [a,b] ↔
      boxIndex D s (a:ℝ) ≥ boxIndex D s (b:ℝ) ∧
      3*exponent s (boxIndex D s (a:ℝ))<1 := by
  rw [outerTest_pair]
  apply and_congr_right
  intro _
  change (D ^ exponent s (boxIndex D s (a:ℝ)))^3 < D ↔
    3*exponent s (boxIndex D s (a:ℝ))<1
  rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : 0≤D)]
  have he : D^(exponent s (boxIndex D s (a:ℝ))*3)<D ↔
      exponent s (boxIndex D s (a:ℝ))*3<1 := by
    simpa only [Real.rpow_one] using
      (Real.rpow_lt_rpow_left_iff (y:=exponent s (boxIndex D s (a:ℝ))*3) (z:=1) hD :
        D^(exponent s (boxIndex D s (a:ℝ))*3)<D^(1:ℝ) ↔
        exponent s (boxIndex D s (a:ℝ))*3<1)
  exact he.trans (by constructor <;> intro h <;> nlinarith)

/-- Literal outer-family membership for a pair, including both pool tests. -/
theorem mem_outerFamily_pair (D s z : ℝ) (hD : 1<D) (hs : 0<s)
    (a b : ℕ) :
    [a,b]∈SieveUpperBoxing.outerFamily D s z ↔
      a∈pool D s z ∧ b∈pool D s z ∧
      boxIndex D s (a:ℝ)≥boxIndex D s (b:ℝ) ∧
      3*exponent s (boxIndex D s (a:ℝ))<1 := by
  rw [SieveUpperBoxing.mem_outerFamily D s z hD hs [a,b],outerTest_pair_index D s hD]
  simp only [List.forall_mem_cons]
  tauto

/-- The actual long-pair source now exposes its geometric box gate. -/
theorem mem_long_pair_source (X s : ℝ) (P : Finset ℕ) (z : ℝ→ℝ)
    (hD : ∀p∈P,1<level X s/p) (hs : 0<s)
    (p d a b : ℕ) :
    (p,d,[a,b])∈LongPairCollectionWork.source X s P z ↔
      p∈P ∧ d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s ∧
      a∈pool (level X s/p) s (z p) ∧
      b∈pool (level X s/p) s (z p) ∧
      boxIndex (level X s/p) s (a:ℝ)≥boxIndex (level X s/p) s (b:ℝ) ∧
      3*exponent s (boxIndex (level X s/p) s (a:ℝ))<1 ∧
      LongerTupleSector.allLong X [a,b] ∧ X^(109/200:ℝ)<(index (p,d,[a,b]):ℝ) := by
  rw [LongPairCollectionWork.mem_source]
  constructor
  · rintro ⟨hp,hd,ht,_,hl,hhigh⟩
    obtain ⟨ha,hb,horder,hgate⟩ := (mem_outerFamily_pair _ _ _ (hD p hp) hs a b).mp ht
    exact ⟨hp,hd,ha,hb,horder,hgate,hl,hhigh⟩
  · rintro ⟨hp,hd,ha,hb,horder,hgate,hl,hhigh⟩
    exact ⟨hp,hd,(mem_outerFamily_pair _ _ _ (hD p hp) hs a b).mpr
      ⟨ha,hb,horder,hgate⟩,by simp,hl,hhigh⟩

run_cmd do
  for decl in [``outerTest_pair, ``outerTest_pair_index, ``mem_outerFamily_pair,
      ``mem_long_pair_source] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPairBoxGateWork
