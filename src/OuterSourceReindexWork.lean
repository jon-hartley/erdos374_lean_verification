import OuterCompletedPrimeSumsWork

/-! Reindex the entire ordered source by its small divisor and tuple,
then its outer prime. Source representations and multiplicities are exact. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace OuterSourceReindexWork
open LongerTupleEncoding PositiveSharpBoxedCount LongPairCloseDistinctMeanWork

abbrev Slice := ℕ×ℕ×ℕ

def drop (r : Representation) : Slice :=
  (r.2.1,ShortPairSplitWork.prime false r,ShortPairSplitWork.prime true r)

def rebuild (u : Slice) (p : ℕ) : Representation := (p,u.1,[u.2.1,u.2.2])

def split (r : Representation) : Slice×ℕ := (drop r,r.1)

theorem rebuild_drop (r : Representation) (hr : r.2.2.length=2) :
    rebuild (drop r) r.1 = r := by
  rcases r with ⟨p,d,t⟩
  obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hr
  simp [rebuild,drop,ShortPairSplitWork.prime]

theorem drop_rebuild (u : Slice) (p : ℕ) : drop (rebuild u p)=u := by
  simp [drop,rebuild,ShortPairSplitWork.prime]

theorem split_injective (r t : Representation)
    (hr : r.2.2.length=2) (ht : t.2.2.length=2) (he : split r=split t) : r=t := by
  have hd := (Prod.mk.inj he).1
  have hp := (Prod.mk.inj he).2
  rw [←rebuild_drop r hr,←rebuild_drop t ht,hd,hp]

def completedPairs (S : Finset Representation) (P : Finset ℕ) : Finset (Slice×ℕ) :=
  ((S.image drop) ×ˢ P).filter (fun u => rebuild u.1 u.2∈S)

theorem completedPairs_eq_image (S : Finset Representation) (P : Finset ℕ)
    (hlen : ∀r∈S,r.2.2.length=2) (hp : ∀r∈S,r.1∈P) :
    completedPairs S P=S.image split := by
  ext u
  constructor
  · intro hu
    obtain ⟨_,hr⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_image.mpr ⟨rebuild u.1 u.2,hr,
      Prod.ext (drop_rebuild _ _) rfl⟩
  · intro hu
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨r,hr,rfl⟩,hp r hr⟩,
      by simpa only [split,rebuild_drop r (hlen r hr)] using hr⟩

theorem completion_sum {M : Type*} [AddCommMonoid M]
    (S : Finset Representation) (P : Finset ℕ)
    (hlen : ∀r∈S,r.2.2.length=2) (hp : ∀r∈S,r.1∈P)
    (f : Representation→M) :
    (∑r∈S,f r) = ∑u∈S.image drop, ∑p∈P,
      if rebuild u p∈S then f (rebuild u p) else 0 := by
  have he : (∑u∈completedPairs S P,f (rebuild u.1 u.2)) = ∑r∈S,f r := by
    rw [completedPairs_eq_image S P hlen hp,Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [split,rebuild_drop r (hlen r hr)]
    · intro r hr t ht he
      exact split_injective r t (hlen r hr) (hlen t ht) he
  rw [←he]
  simp only [completedPairs,Finset.sum_filter,Finset.sum_product]

theorem separated_source_data (X s : ℝ) (r : Representation)
    (hr : r∈separatedSource X s) : r.2.2.length=2 ∧ r.1∈largePrimes X := by
  simp only [separatedSource,LongPairRepeatedCoreMeanWork.distinctSource,
    LongPairTwoSidedCoreMeanWork.twoSidedCoreSource,
    LongPairHighCoreMeanWork.highCoreSource,LongPairHighStripWork.highSource,
    Finset.mem_filter] at hr
  have hb := (LongPairCollectionWork.mem_source X s _ _ r).mp hr.1.1.1.1.1
  exact ⟨hb.2.2.2.1,hb.1⟩

def slices (X s : ℝ) : Finset Slice := (separatedSource X s).image drop

theorem separated_completion_sum {M : Type*} [AddCommMonoid M]
    (X s : ℝ) (f : Representation→M) :
    (∑r∈separatedSource X s,f r) = ∑u∈slices X s, ∑p∈largePrimes X,
      if rebuild u p∈separatedSource X s then f (rebuild u p) else 0 :=
  completion_sum (separatedSource X s) (largePrimes X)
    (fun r hr => (separated_source_data X s r hr).1)
    (fun r hr => (separated_source_data X s r hr).2) f

run_cmd do
  for decl in [``rebuild_drop, ``drop_rebuild, ``split_injective,
      ``completedPairs_eq_image, ``completion_sum, ``separated_source_data,
      ``separated_completion_sum] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSourceReindexWork
