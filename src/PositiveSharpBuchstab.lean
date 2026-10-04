import PositiveBuchstabRepresentations
import PositiveSharpCounts
import PositiveSharpOrdering

/-! The actual retained prime-coordinate count injects into the positive
ordered Buchstab term. Product coincidences and equal p,r are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace PositiveSharpBuchstab
open PositiveSharpCounts PositiveInteriorModel PositiveInteriorCells
open PositiveBuchstabRepresentations Erdos374.HarmanAnalytic151

abbrev IndexedTriple := Σ _j : ℕ × ℕ, Triple
def retained (X x y : ℝ) : Finset IndexedTriple :=
  (boxes (mesh X)).sigma fun j => (windowTuples X j x y).filter allPrime
def window (x y : ℝ) : Finset ℕ := Finset.Ioc ⌊x-y⌋₊ ⌊x⌋₊
def firstCutoff (X : ℝ) : ℕ := ⌈X^(9/35:ℝ)⌉₊
def lastCutoff (X : ℝ) : ℕ := ⌈Real.sqrt X⌉₊
def innerCutoff (X s : ℝ) (p : ℕ) : ℕ := ⌈(X^(1-3*s)/(p:ℝ))^(1/3:ℝ)⌉₊
def sourceTerm (X s x y : ℝ) : ℕ :=
  ∑ p ∈ primeBand (firstCutoff X) (lastCutoff X),
    ∑ q ∈ primeBand (innerCutoff X s p) p,
      (sifted (divisorSlice (window x y) (p*q)) q).card
def representation (t : IndexedTriple) : Representation :=
  ⟨t.2.1,⟨t.2.2.2,natProduct t.2⟩⟩

theorem mem_retained (X x y : ℝ) (t : IndexedTriple) :
    t∈retained X x y ↔ t.1∈boxes (mesh X) ∧
      t.2∈coordinates X t.1 ∧ inWindow x y t.2 ∧ allPrime t.2 := by
  simp only [retained, Finset.mem_sigma, Finset.mem_filter, windowTuples, and_assoc]

theorem card_retained (X x y : ℝ) :
    (retained X x y).card=∑ j∈boxes (mesh X), primeCount X j x y := by
  simp only [retained, Finset.card_sigma, primeCount]

theorem representation_mem (X x y s : ℝ) (hX : 1<X)
    (hx : X≤x ∧ x≤2*X) (hy : 0<y ∧ y≤X/2)
    (hm : mesh X≤1/3200) (hs : 0≤s)
    (t : IndexedTriple) (ht : t∈retained X x y) :
    representation t ∈ representations (window x y) (firstCutoff X) (lastCutoff X)
      (innerCutoff X s) := by
  obtain ⟨hj,hcoord,hw,hprime⟩ := (mem_retained X x y t).mp ht
  have hb := coordinates_bounds X (by linarith) t.1 t.2 hcoord
  have ho := PositiveSharpOrdering.actual_ordering X x y s t.1 t.2.1 t.2.2.1 t.2.2.2
    hX hx hy hj hm hs hb.1 hb.2.1 hw
  have hpband : t.2.1∈primeBand (firstCutoff X) (lastCutoff X) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨Nat.ceil_le.mpr ho.1.le,Nat.lt_ceil.mpr ho.2.1⟩,hprime.1⟩
  have hqband : t.2.2.2∈primeBand (innerCutoff X s t.2.1) t.2.1 := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨Nat.ceil_le.mpr ho.2.2.2.2.le,ho.2.2.1⟩,hprime.2.2⟩
  have hA : natProduct t.2∈window x y := by
    have hlo : 0≤x-y := by linarith [hx.1,hy.2]
    have hx0 : 0≤x := by linarith [hx.1]
    apply Finset.mem_Ioc.mpr
    exact ⟨(Nat.floor_lt hlo).mpr (by simpa only [natProduct_cast] using hw.1),
      (Nat.le_floor_iff hx0).mpr (by simpa only [natProduct_cast] using hw.2)⟩
  exact triple_mem (window x y) (firstCutoff X) (lastCutoff X) (innerCutoff X s)
    t.2.1 t.2.2.1 t.2.2.2 hpband hqband hprime.2.1 ho.2.2.2.1.le hA

theorem representation_injective (X x y : ℝ) (hX : 0<X) :
    Set.InjOn representation (retained X x y : Set IndexedTriple) := by
  intro t ht u hu he
  obtain ⟨_,htc,_,htp⟩ := (mem_retained X x y t).mp ht
  obtain ⟨_,huc,_,_⟩ := (mem_retained X x y u).mp hu
  have hp : t.2.1=u.2.1 := congrArg (fun v : Representation => v.1) he
  have hq : t.2.2.2=u.2.2.2 := congrArg (fun v : Representation => v.2.1) he
  have hn : natProduct t.2=natProduct u.2 := congrArg (fun v : Representation => v.2.2) he
  have hr : t.2.2.1=u.2.2.1 := cancel_middle t.2.1 t.2.2.2 t.2.2.1 u.2.2.1
    htp.1.pos htp.2.2.pos (by simpa only [natProduct, ←hp, ←hq] using hn)
  have hk : t.2=u.2 := Prod.ext hp (Prod.ext hr hq)
  have htb := coordinates_bounds X hX t.1 t.2 htc
  have hub := coordinates_bounds X hX u.1 u.2 huc
  have hj : t.1=u.1 := PositiveSharpOrdering.dyadic_pair_unique
    (t.2.1:ℝ) (t.2.2.1:ℝ) t.1 u.1 htb.1 htb.2.1
      (by simpa only [hp] using hub.1) (by simpa only [hr] using hub.2.1)
  exact Sigma.ext hj (heq_of_eq hk)

theorem retained_count_le_source (X x y s : ℝ) (hX : 1<X)
    (hx : X≤x ∧ x≤2*X) (hy : 0<y ∧ y≤X/2)
    (hm : mesh X≤1/3200) (hs : 0≤s) :
    (∑ j∈boxes (mesh X), primeCount X j x y)≤sourceTerm X s x y := by
  rw [←card_retained, sourceTerm, ←card_representations]
  exact Finset.card_le_card_of_injOn representation
    (fun t ht => representation_mem X x y s hX hx hy hm hs t ht)
    (representation_injective X x y (by linarith))

run_cmd do
  for decl in [``mem_retained, ``card_retained, ``representation_mem,
      ``representation_injective, ``retained_count_le_source] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ORDERED PRIME COUNT INJECTS INTO POSITIVE BUCHSTAB TERM"
end PositiveSharpBuchstab
end
