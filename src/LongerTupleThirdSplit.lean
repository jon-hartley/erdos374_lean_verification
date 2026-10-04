import LongerTupleEncoding

/-! Exact third-entry separation retaining ordered list representations.
The completion sum ranges over actual drop images and a finite prime set;
its membership predicate restores precisely the original family. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongerTupleThirdSplit
open LongerTupleEncoding (Representation index)

def erase (t : List ℕ) : List ℕ := t.take 2 ++ t.drop 3
def third (t : List ℕ) : ℕ := t.getD 2 1
def insert (q : ℕ) (t : List ℕ) : List ℕ := t.take 2 ++ q :: t.drop 2

theorem exists_three (t : List ℕ) (ht : 3 ≤ t.length) :
    ∃ a b q tail, t = a :: b :: q :: tail := by
  cases t with
  | nil => simp at ht
  | cons a t =>
    cases t with
    | nil => simp at ht
    | cons b t =>
      cases t with
      | nil => simp at ht
      | cons q tail => exact ⟨a, b, q, tail, rfl⟩

theorem exists_two (t : List ℕ) (ht : 2 ≤ t.length) :
    ∃ a b tail, t = a :: b :: tail := by
  cases t with
  | nil => simp at ht
  | cons a t =>
    cases t with
    | nil => simp at ht
    | cons b tail => exact ⟨a, b, tail, rfl⟩

theorem insert_erase (t : List ℕ) (ht : 3 ≤ t.length) :
    insert (third t) (erase t) = t := by
  obtain ⟨a, b, q, tail, rfl⟩ := exists_three t ht
  simp [insert, third, erase]

theorem erase_insert (q : ℕ) (t : List ℕ) (ht : 2 ≤ t.length) :
    erase (insert q t) = t := by
  obtain ⟨a, b, tail, rfl⟩ := exists_two t ht
  simp [insert, erase]

theorem third_insert (q : ℕ) (t : List ℕ) (ht : 2 ≤ t.length) :
    third (insert q t) = q := by
  obtain ⟨a, b, tail, rfl⟩ := exists_two t ht
  simp [insert, third]

theorem erase_length (t : List ℕ) (ht : 3 ≤ t.length) :
    (erase t).length + 1 = t.length := by
  obtain ⟨a, b, q, tail, rfl⟩ := exists_three t ht
  simp [erase]

theorem erase_length_two (t : List ℕ) (ht : 3 ≤ t.length) :
    2 ≤ (erase t).length := by
  have hh := erase_length t ht
  omega

theorem insert_length (q : ℕ) (t : List ℕ) (ht : 2 ≤ t.length) :
    (insert q t).length = t.length + 1 := by
  obtain ⟨a, b, tail, rfl⟩ := exists_two t ht
  simp [insert]

theorem prod_erase_third (t : List ℕ) (ht : 3 ≤ t.length) :
    t.prod = (erase t).prod * third t := by
  obtain ⟨a, b, q, tail, rfl⟩ := exists_three t ht
  change a * (b * (q * tail.prod)) = (a * (b * tail.prod)) * q
  ring

def drop (a : Representation) : Representation := (a.1, a.2.1, erase a.2.2)
def rebuild (a : Representation) (q : ℕ) : Representation :=
  (a.1, a.2.1, insert q a.2.2)
def split (a : Representation) : Representation × ℕ := (drop a, third a.2.2)

theorem rebuild_drop (a : Representation) (ha : 3 ≤ a.2.2.length) :
    rebuild (drop a) (third a.2.2) = a := by
  simp only [rebuild, drop, insert_erase _ ha]

theorem drop_rebuild (a : Representation) (q : ℕ) (ha : 2 ≤ a.2.2.length) :
    drop (rebuild a q) = a := by
  simp only [rebuild, drop, erase_insert _ _ ha]

theorem third_rebuild (a : Representation) (q : ℕ) (ha : 2 ≤ a.2.2.length) :
    third (rebuild a q).2.2 = q := third_insert q a.2.2 ha

theorem index_drop (a : Representation) (ha : 3 ≤ a.2.2.length) :
    index a = index (drop a) * third a.2.2 := by
  unfold index drop
  rw [prod_erase_third a.2.2 ha]
  ring

theorem split_injective (a b : Representation)
    (ha : 3 ≤ a.2.2.length) (hb : 3 ≤ b.2.2.length) (hab : split a = split b) : a = b := by
  have hd := (Prod.mk.inj hab).1
  have hq := (Prod.mk.inj hab).2
  rw [← rebuild_drop a ha, ← rebuild_drop b hb]
  rw [hd, hq]

def completedPairs (A : Finset Representation) (B : Finset ℕ) :
    Finset (Representation × ℕ) :=
  ((A.image drop) ×ˢ B).filter (fun u => rebuild u.1 u.2 ∈ A)

theorem completedPairs_eq_image (A : Finset Representation) (B : Finset ℕ)
    (hA : ∀ a ∈ A, 3 ≤ a.2.2.length) (hB : ∀ a ∈ A, third a.2.2 ∈ B) :
    completedPairs A B = A.image split := by
  ext u
  constructor
  · intro hu
    obtain ⟨hu, hr⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu₁, _⟩ := Finset.mem_product.mp hu
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hu₁
    have huLen : 2 ≤ u.1.2.2.length := by
      rw [← he]
      exact erase_length_two a.2.2 (hA a ha)
    apply Finset.mem_image.mpr
    refine ⟨rebuild u.1 u.2, hr, ?_⟩
    exact Prod.ext (drop_rebuild u.1 u.2 huLen) (third_rebuild u.1 u.2 huLen)
  · intro hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, hB a ha⟩, ?_⟩
    simpa only [split, rebuild_drop a (hA a ha)] using ha

theorem completion_sum {M : Type*} [AddCommMonoid M]
    (A : Finset Representation) (B : Finset ℕ)
    (hA : ∀ a ∈ A, 3 ≤ a.2.2.length) (hB : ∀ a ∈ A, third a.2.2 ∈ B)
    (f : Representation → M) :
    (∑ a ∈ A, f a) =
      ∑ a ∈ A.image drop, ∑ q ∈ B, if rebuild a q ∈ A then f (rebuild a q) else 0 := by
  have hh : (∑ u ∈ completedPairs A B, f (rebuild u.1 u.2)) = ∑ a ∈ A, f a := by
    rw [completedPairs_eq_image A B hA hB, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [split, rebuild_drop a (hA a ha)]
    · intro a ha b hb hab
      exact split_injective a b (hA a ha) (hA b hb) hab
  rw [← hh]
  simp only [completedPairs, Finset.sum_filter, Finset.sum_product]

run_cmd do
  for decl in [``exists_three, ``exists_two, ``insert_erase, ``erase_insert,
      ``third_insert, ``erase_length, ``erase_length_two, ``insert_length,
      ``prod_erase_third, ``rebuild_drop, ``drop_rebuild, ``third_rebuild,
      ``index_drop, ``split_injective, ``completedPairs_eq_image, ``completion_sum] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT THIRD PRIME SPLIT AND COMPLETION SUM PASSED"

end LongerTupleThirdSplit
