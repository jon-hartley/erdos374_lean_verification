import LongerTupleCollection
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

/-! Exact collection of (p,d,t), where t is an ordered list of fixed length.
The entries need not be distinct or ordered by size. Their original positions
are retained, so different factorizations contribute separately to the fiber. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongerTupleEncoding

abbrev Representation := ℕ × ℕ × List ℕ

def listEncoding (k : ℕ) (t : List ℕ) : Fin k → ℕ := fun i => t.getD i 1

theorem ofFn_listEncoding (k : ℕ) (t : List ℕ) (ht : t.length = k) :
    List.ofFn (listEncoding k t) = t := by
  apply List.ext_getElem
  · simp [ht]
  · intro i hi₁ hi₂
    simp only [List.getElem_ofFn, listEncoding]
    exact (List.getElem_eq_getD 1).symm

theorem listEncoding_prod (k : ℕ) (t : List ℕ) (ht : t.length = k) :
    (∏ i, listEncoding k t i) = t.prod := by
  rw [← List.prod_ofFn, ofFn_listEncoding k t ht]

def encode (k : ℕ) (a : Representation) : Fin (k+2) → ℕ :=
  Fin.cons a.1 (Fin.cons a.2.1 (listEncoding k a.2.2))

def index (a : Representation) : ℕ := a.1 * a.2.1 * a.2.2.prod

theorem encode_product (k : ℕ) (a : Representation) (ha : a.2.2.length = k) :
    index a = ∏ i, encode k a i := by
  simp only [encode, Fin.prod_cons, listEncoding_prod k a.2.2 ha, index]
  exact Nat.mul_assoc _ _ _

theorem encode_injective (k : ℕ) (a b : Representation)
    (ha : a.2.2.length = k) (hb : b.2.2.length = k)
    (hab : encode k a = encode k b) : a = b := by
  have hp : a.1 = b.1 := by
    have hh := congrFun hab 0
    simpa only [encode, Fin.cons_zero] using hh
  have hd : a.2.1 = b.2.1 := by
    have hh := congrFun hab (Fin.succ 0)
    simpa only [encode, Fin.cons_succ, Fin.cons_zero] using hh
  have ht : listEncoding k a.2.2 = listEncoding k b.2.2 := by
    funext i
    have hh := congrFun hab i.succ.succ
    simpa only [encode, Fin.cons_succ] using hh
  have ht' : a.2.2 = b.2.2 := by
    rw [← ofFn_listEncoding k a.2.2 ha, ← ofFn_listEncoding k b.2.2 hb, ht]
  exact Prod.ext hp (Prod.ext hd ht')

theorem fiber_card_le (k : ℕ) (S : Finset Representation)
    (hS : ∀ a ∈ S, a.2.2.length = k) (n : ℕ) (hn : n ≠ 0) :
    (S.filter (fun a => index a = n)).card ≤ n.divisors.card^(k+2) := by
  apply LongerTupleCollection.fiber_card_le (k+2) S index (encode k)
  · intro a ha
    exact encode_product k a (hS a ha)
  · intro a ha b hb hab
    exact encode_injective k a b (hS a ha) (hS b hb) hab
  · exact hn

theorem coefficient_norm_le (k : ℕ) (S : Finset Representation)
    (hS : ∀ a ∈ S, a.2.2.length = k) (w : Representation → ℂ)
    (hw : ∀ a ∈ S, ‖w a‖ ≤ 1) (n : ℕ) (hn : n ≠ 0) :
    ‖LongerTupleCollection.coefficient S index w n‖ ≤
      (n.divisors.card : ℝ)^(k+2) := by
  apply LongerTupleCollection.coefficient_norm_le (k+2) S index (encode k)
  · intro a ha
    exact encode_product k a (hS a ha)
  · intro a ha b hb hab
    exact encode_injective k a b (hS a ha) (hS b hb) hab
  · exact hw
  · exact hn

theorem eventual_coefficient_cap (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (S : Finset Representation) (w : Representation → ℂ),
        (∀ a ∈ S, a.2.2.length = k) → (∀ a ∈ S, ‖w a‖ ≤ 1) →
        ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X^2 →
          ‖LongerTupleCollection.coefficient S index w n‖ ≤ X^δ := by
  filter_upwards [LongerTupleCollection.eventually_divisor_power_cap (k+2) δ hδ]
    with X hX
  refine ⟨hX.1, ?_⟩
  intro S w hS hw n hn hnX
  exact (coefficient_norm_le k S hS w hw n (by omega)).trans (hX.2 n hnX)

run_cmd do
  for decl in [``ofFn_listEncoding, ``listEncoding_prod, ``encode_product,
      ``encode_injective, ``fiber_card_le, ``coefficient_norm_le,
      ``eventual_coefficient_cap] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FIXED LENGTH ORDERED PRIME-DIVISOR REPRESENTATIONS PASSED"

end LongerTupleEncoding
