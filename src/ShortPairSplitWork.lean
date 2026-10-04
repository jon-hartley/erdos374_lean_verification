import LongerTupleHigherMeanWork

/-! Exact ordered length-two splitting. `second=true` distinguishes the
second prime; `second=false` distinguishes the first. No collisions are lost. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ShortPairSplitWork
open LongerTupleEncoding (Representation)

abbrev PairRep := ℕ × ℕ × ℕ
def index (a : PairRep) : ℕ := a.1*a.2.1*a.2.2
def encode (a : PairRep) : Fin 3 → ℕ := Fin.cons a.1 (Fin.cons a.2.1 (Fin.cons a.2.2 Fin.elim0))
def drop (second : Bool) (r : Representation) : PairRep :=
  (r.1,r.2.1,r.2.2.getD (if second then 0 else 1) 1)
def prime (second : Bool) (r : Representation) : ℕ :=
  r.2.2.getD (if second then 1 else 0) 1
def rebuild (second : Bool) (a : PairRep) (q : ℕ) : Representation :=
  (a.1,a.2.1,if second then [a.2.2,q] else [q,a.2.2])
def split (second : Bool) (r : Representation) : PairRep × ℕ := (drop second r,prime second r)

theorem encode_product (a : PairRep) : index a = ∏ i, encode a i := by
  simp [index,encode,Fin.prod_cons,Nat.mul_assoc]

theorem encode_injective : Function.Injective encode := by
  intro a b he
  have hp := congrFun he 0
  have hd := congrFun he (Fin.succ 0)
  have hq := congrFun he (Fin.succ (Fin.succ 0))
  simp only [encode,Fin.cons_zero,Fin.cons_succ] at hp hd hq
  exact Prod.ext hp (Prod.ext hd hq)

theorem rebuild_drop (second : Bool) (r : Representation) (hr : r.2.2.length = 2) :
    rebuild second (drop second r) (prime second r) = r := by
  rcases r with ⟨p,d,t⟩
  obtain ⟨u,v,rfl⟩ := List.length_eq_two.mp hr
  cases second <;> simp [rebuild,drop,prime]

theorem drop_rebuild (second : Bool) (a : PairRep) (q : ℕ) :
    drop second (rebuild second a q) = a := by
  cases second <;> simp [drop,rebuild]

theorem prime_rebuild (second : Bool) (a : PairRep) (q : ℕ) :
    prime second (rebuild second a q) = q := by
  cases second <;> simp [prime,rebuild]

theorem index_rebuild (second : Bool) (a : PairRep) (q : ℕ) :
    LongerTupleEncoding.index (rebuild second a q) = index a*q := by
  cases second <;> simp [LongerTupleEncoding.index,index,rebuild] <;> ring

theorem index_drop (second : Bool) (r : Representation) (hr : r.2.2.length = 2) :
    LongerTupleEncoding.index r = index (drop second r)*prime second r := by
  rw [←rebuild_drop second r hr,index_rebuild,drop_rebuild,prime_rebuild]

theorem prime_mem (second : Bool) (r : Representation) (hr : r.2.2.length = 2) :
    prime second r ∈ r.2.2 := by
  rcases r with ⟨p,d,t⟩
  obtain ⟨u,v,rfl⟩ := List.length_eq_two.mp hr
  cases second <;> simp [prime]

theorem split_injective (second : Bool) (a b : Representation)
    (ha : a.2.2.length = 2) (hb : b.2.2.length = 2) (he : split second a = split second b) : a=b := by
  have hd := (Prod.mk.inj he).1
  have hq := (Prod.mk.inj he).2
  rw [←rebuild_drop second a ha,←rebuild_drop second b hb,hd,hq]

def completedPairs (second : Bool) (S : Finset Representation) (B : Finset ℕ) :
    Finset (PairRep × ℕ) :=
  ((S.image (drop second)) ×ˢ B).filter (fun u => rebuild second u.1 u.2 ∈ S)

theorem completedPairs_eq_image (second : Bool) (S : Finset Representation) (B : Finset ℕ)
    (hlen : ∀ r ∈ S, r.2.2.length = 2) (hp : ∀ r ∈ S, prime second r ∈ B) :
    completedPairs second S B = S.image (split second) := by
  ext u
  constructor
  · intro hu
    obtain ⟨hu,hc⟩ := Finset.mem_filter.mp hu
    apply Finset.mem_image.mpr
    exact ⟨rebuild second u.1 u.2,hc,Prod.ext (drop_rebuild _ _ _) (prime_rebuild _ _ _)⟩
  · intro hu
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hu
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨r,hr,rfl⟩,hp r hr⟩,
      by simpa only [split,rebuild_drop second r (hlen r hr)] using hr⟩

theorem completion_sum {M : Type*} [AddCommMonoid M]
    (second : Bool) (S : Finset Representation) (B : Finset ℕ)
    (hlen : ∀ r ∈ S, r.2.2.length = 2) (hp : ∀ r ∈ S, prime second r ∈ B)
    (f : Representation → M) :
    (∑ r ∈ S,f r) = ∑ a ∈ S.image (drop second), ∑ q ∈ B,
      if rebuild second a q ∈ S then f (rebuild second a q) else 0 := by
  have he : (∑ u ∈ completedPairs second S B,f (rebuild second u.1 u.2)) = ∑ r ∈ S,f r := by
    rw [completedPairs_eq_image second S B hlen hp,Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [split,rebuild_drop second r (hlen r hr)]
    · intro a ha b hb he
      exact split_injective second a b (hlen a ha) (hlen b hb) he
  rw [←he]
  simp only [completedPairs,Finset.sum_filter,Finset.sum_product]

run_cmd do
  for decl in [``encode_product, ``encode_injective, ``rebuild_drop, ``drop_rebuild,
      ``prime_rebuild, ``index_rebuild, ``index_drop, ``prime_mem, ``split_injective,
      ``completedPairs_eq_image, ``completion_sum] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT ORDERED SHORT PAIR SPLIT PASSED"

end ShortPairSplitWork
