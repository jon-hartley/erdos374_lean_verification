import SieveMarkedDeletion
import SieveThinPrimeInterval

/-! An actual all-length cubic-strip bound. A witness coordinate is selected
for each tuple. Deleting that coordinate fixes its preceding product inside
each fiber, so the proved prime interval bound applies without any further
distribution hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace SieveCubicStripMass
open SieveMarkedDeletion SieveThinPrimeInterval

theorem marked_cubic_strip_mass_le (D s z α β : ℝ)
    (F : Finset (List ℕ)) (L : ℕ) (mark pos : List ℕ → ℕ)
    (hD : 1 < D) (hs : 0 < s) (hwidth : β-α ≤ s^9)
    (hstrict : ∀ t ∈ F, t.Pairwise (· > ·))
    (hpool : ∀ t ∈ F, ∀ p ∈ t, p ∈ SieveBoxedFamily.pool D s z)
    (hlength : ∀ t ∈ F, t.length ≤ L)
    (hindex : ∀ t ∈ F, pos t < t.length)
    (hmark : ∀ t (ht : t ∈ F), mark t = t[pos t]'(hindex t ht))
    (hstrip : ∀ t ∈ F,
      D^α ≤ ((t.take (pos t)).prod : ℝ)*(mark t : ℝ)^3 ∧
        ((t.take (pos t)).prod : ℝ)*(mark t : ℝ)^3 < D^β) :
    (∑ t ∈ F, SieveBoxMass.reciprocal t) ≤
      (L : ℝ) * delta D s *
        ∏ p ∈ SieveBoxedFamily.pool D s z, (1 + (p : ℝ)⁻¹) := by
  classical
  have hmem : ∀ t ∈ F, mark t ∈ t := by
    intro t ht
    rw [hmark t ht]
    exact List.getElem_mem (hindex t ht)
  apply reciprocal_mass_le F (SieveBoxedFamily.pool D s z) mark pos L (delta D s)
    hstrict hpool hmem (fun t ht => (hindex t ht).trans_le (hlength t ht))
  intro i _ R _
  by_cases hne : (fiber F mark pos i R).Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    obtain ⟨t₀, ht₀, hi₀, hR₀, _⟩ := (mem_fiber F mark pos i R p₀).mp hp₀
    have hA : 0 < ((t₀.take i).prod : ℝ) := by
      apply Nat.cast_pos.mpr
      apply List.prod_pos
      intro p hp
      exact ((SieveBoxedFamily.mem_pool D s z p).mp
        (hpool t₀ ht₀ p (List.mem_of_mem_take hp))).1.pos
    apply cubic_strip_bound D s ((t₀.take i).prod : ℝ) α β
      (fiber F mark pos i R) hD hs hA hwidth
    intro p hp
    obtain ⟨t, ht, hi, hR, hm⟩ := (mem_fiber F mark pos i R p).mp hp
    have hpPool := (SieveBoxedFamily.mem_pool D s z p).mp
      (hpool t ht p (hm ▸ hmem t ht))
    refine ⟨hpPool.1, hpPool.2.2, ?_⟩
    have hit : i < t.length := hi ▸ hindex t ht
    have hi₀t : i < t₀.length := hi₀ ▸ hindex t₀ ht₀
    have hmt : mark t = t[i] := by simpa only [hi] using hmark t ht
    have hm₀ : mark t₀ = t₀[i] := by simpa only [hi₀] using hmark t₀ ht₀
    have htake := take_eq_of_residual_eq mark t t₀ i (hstrict t ht) (hstrict t₀ ht₀)
      hit hi₀t hmt hm₀ (hR.trans hR₀.symm)
    have hg := hstrip t ht
    simpa only [hi, htake, hm] using hg
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact delta_nonneg D s hD hs

/-- It suffices for each actual prime tuple to have one cubic-strip witness;
no fixed tuple length or selected witness is part of the hypothesis. -/
theorem cubic_strip_mass_le (D s z α β : ℝ) (F : Finset (List ℕ)) (L : ℕ)
    (hD : 1 < D) (hs : 0 < s) (hwidth : β-α ≤ s^9)
    (hstrict : ∀ t ∈ F, t.Pairwise (· > ·))
    (hpool : ∀ t ∈ F, ∀ p ∈ t, p ∈ SieveBoxedFamily.pool D s z)
    (hlength : ∀ t ∈ F, t.length ≤ L)
    (hstrip : ∀ t ∈ F, ∃ (i : ℕ) (hi : i < t.length),
      D^α ≤ ((t.take i).prod : ℝ)*(t[i] : ℝ)^3 ∧
        ((t.take i).prod : ℝ)*(t[i] : ℝ)^3 < D^β) :
    (∑ t ∈ F, SieveBoxMass.reciprocal t) ≤
      (L : ℝ) * delta D s *
        ∏ p ∈ SieveBoxedFamily.pool D s z, (1 + (p : ℝ)⁻¹) := by
  classical
  let pos : List ℕ → ℕ := fun t => if ht : t ∈ F then (hstrip t ht).choose else 0
  have hchosen : ∀ t ∈ F, ∃ (hi : pos t < t.length),
      D^α ≤ ((t.take (pos t)).prod : ℝ)*(t[pos t] : ℝ)^3 ∧
        ((t.take (pos t)).prod : ℝ)*(t[pos t] : ℝ)^3 < D^β := by
    intro t ht
    simpa only [pos, dite_eq_left ht] using (hstrip t ht).choose_spec
  have hindex : ∀ t ∈ F, pos t < t.length := fun t ht => (hchosen t ht).choose
  let mark : List ℕ → ℕ := fun t => t.getD (pos t) 0
  have hmark : ∀ t (ht : t ∈ F), mark t = t[pos t]'(hindex t ht) := by
    intro t ht
    simp only [mark, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hindex t ht),
      Option.getD_some]
  apply marked_cubic_strip_mass_le D s z α β F L mark pos hD hs hwidth
    hstrict hpool hlength hindex hmark
  intro t ht
  rw [hmark t ht]
  exact (hchosen t ht).choose_spec

run_cmd do
  for decl in [``marked_cubic_strip_mass_le, ``cubic_strip_mass_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ALL-LENGTH CUBIC STRIP RECIPROCAL MASS BOUND"

end SieveCubicStripMass
end
