import SievePrefix
import Mathlib.Data.List.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
attribute [local instance] Classical.propDecidable

namespace SievePrefix

def accepts (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ) : List ℕ → Prop
  | [] => True
  | p :: ps => (upper = false ∨ gate d p) ∧ accepts gate (!upper) (d*p) ps

theorem empty_mem_selected (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) : ∅ ∈ selected gate upper d ps := by
  induction ps with
  | nil => simp [selected]
  | cons p ps ih => exact Finset.mem_union_left _ ih

theorem selected_of_sublist_accepts (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps qs : List ℕ) (hsub : qs.Sublist ps) (ha : accepts gate upper d qs) :
    qs.toFinset ∈ selected gate upper d ps := by
  induction ps generalizing upper d qs with
  | nil =>
    have hq : qs = [] := List.eq_nil_of_sublist_nil hsub
    subst qs
    simp [selected]
  | cons p ps ih =>
    cases qs with
    | nil => exact empty_mem_selected gate upper d (p::ps)
    | cons q qs =>
      rcases List.cons_sublist_cons'.mp hsub with hs | ⟨rfl, hs⟩
      · exact Finset.mem_union_left _ (ih upper d (q::qs) hs ha)
      · obtain ⟨hg, ht⟩ := ha
        simp only [selected, Finset.mem_union]
        right
        rw [ite_eq_left hg]
        exact Finset.mem_image.mpr ⟨qs.toFinset, ih (!upper) (d*q) qs hs ht, by simp⟩

theorem exists_sublist_accepts_of_selected (gate : ℕ → ℕ → Prop) (upper : Bool)
    (d : ℕ) (ps : List ℕ) (s : Finset ℕ) (hs : s ∈ selected gate upper d ps) :
    ∃ qs : List ℕ, qs.Sublist ps ∧ qs.toFinset = s ∧ accepts gate upper d qs := by
  induction ps generalizing upper d s with
  | nil =>
    have he : s = ∅ := by simpa [selected] using hs
    subst s
    exact ⟨[], List.Sublist.refl _, rfl, trivial⟩
  | cons p ps ih =>
    simp only [selected, Finset.mem_union] at hs
    rcases hs with hs | hs
    · obtain ⟨qs, hq, he, ha⟩ := ih upper d s hs
      exact ⟨qs, hq.cons p, he, ha⟩
    · split_ifs at hs with hg
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
        obtain ⟨qs, hq, he, ha⟩ := ih (!upper) (d*p) r hr
        exact ⟨p::qs, hq.cons_cons p, by simp [he], hg, ha⟩
      · simp at hs

theorem mem_selected_iff (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) (s : Finset ℕ) :
    s ∈ selected gate upper d ps ↔
      ∃ qs : List ℕ, qs.Sublist ps ∧ qs.toFinset = s ∧ accepts gate upper d qs := by
  constructor
  · exact exists_sublist_accepts_of_selected gate upper d ps s
  · rintro ⟨qs, hq, rfl, ha⟩
    exact selected_of_sublist_accepts gate upper d ps qs hq ha

theorem accepts_lower_cons_cons (gate : ℕ → ℕ → Prop) (d p q : ℕ) (qs : List ℕ) :
    accepts gate false d (p::q::qs) ↔
      gate (d*p) q ∧ accepts gate false (d*p*q) qs := by
  simp [accepts]

theorem accepts_upper_cons (gate : ℕ → ℕ → Prop) (d p : ℕ) (qs : List ℕ) :
    accepts gate true d (p::qs) ↔ gate d p ∧ accepts gate false (d*p) qs := by
  simp [accepts]

#print axioms mem_selected_iff
run_cmd do
  for decl in [``empty_mem_selected, ``selected_of_sublist_accepts,
      ``exists_sublist_accepts_of_selected, ``mem_selected_iff,
      ``accepts_lower_cons_cons, ``accepts_upper_cons] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SievePrefix
end
