import SieveMarkedDeletion

/-! Repeated bands in decreasing tuples are charged to one deleted coordinate.
A repeated weakly decreasing index sequence has an adjacent repetition. The
deletion position and residual prime subset retain the preceding prime, so the
deleted-coordinate fiber lies in one band. No restriction on tuple length is
discarded, and no injectivity of prime products is used. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace SieveRepeatedBandDeletion

theorem adjacent_repeat (xs : List ℕ) (hweak : xs.Pairwise (· ≥ ·))
    (hdup : ¬xs.Nodup) :
    ∃ j, 0 < j ∧ j < xs.length ∧ xs[j - 1]! = xs[j]! := by
  have hex : ∃ i j, ∃ (hi : i < xs.length) (hj : j < xs.length),
      i < j ∧ xs[i] = xs[j] := by
    by_contra h
    apply hdup
    apply List.nodup_iff_pairwise_ne.mpr
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij heq
    exact h ⟨i, j, hi, hj, hij, heq⟩
  obtain ⟨i, j, hi, hj, hij, heq⟩ := hex
  have hi1 : i + 1 < xs.length := by omega
  refine ⟨i + 1, by omega, hi1, ?_⟩
  rw [Nat.add_sub_cancel, getElem!_pos xs i hi, getElem!_pos xs (i + 1) hi1]
  apply Nat.le_antisymm
  · by_cases he : i + 1 = j
    · subst j
      exact heq.le
    · have hw := hweak.rel_getElem_of_lt hi1 hj (by omega)
      omega
  · exact hweak.rel_getElem_of_lt hi hi1 (by omega)

theorem adjacent_index_repeat (index : ℕ → ℕ) (t : List ℕ)
    (hweak : (t.map index).Pairwise (· ≥ ·))
    (hdup : ¬(t.map index).Nodup) :
    ∃ j, 0 < j ∧ j < t.length ∧ index (t[j - 1]!) = index (t[j]!) := by
  obtain ⟨j, hj0, hj, he⟩ := adjacent_repeat (t.map index) hweak hdup
  have hjt : j < t.length := by simpa only [List.length_map] using hj
  have hjprev : j - 1 < t.length := by omega
  have hjprevMap : j - 1 < (t.map index).length := by simpa using hjprev
  refine ⟨j, hj0, hjt, ?_⟩
  rw [getElem!_pos (t.map index) (j - 1) hjprevMap,
    getElem!_pos (t.map index) j hj] at he
  simpa only [List.getElem_map, getElem!_pos t (j - 1) hjprev,
    getElem!_pos t j hjt] using he

theorem preceding_eq_of_take_eq (t v : List ℕ) (i : ℕ)
    (hi : 0 < i) (hit : i < t.length) (hiv : i < v.length)
    (he : t.take i = v.take i) : t[i - 1]! = v[i - 1]! := by
  have ht : i - 1 < (t.take i).length := by simp only [List.length_take]; omega
  have hv : i - 1 < (v.take i).length := by simp only [List.length_take]; omega
  have h := congrArg (fun xs : List ℕ => xs[i - 1]!) he
  simpa only [getElem!_pos (t.take i) (i - 1) ht,
    getElem!_pos (v.take i) (i - 1) hv, List.getElem_take,
    getElem!_pos t (i - 1) (by omega),
    getElem!_pos v (i - 1) (by omega)] using h

/-- The finite band-mass premise automatically includes its empty-set case. -/
theorem band_bound_nonneg (P : Finset ℕ) (index : ℕ → ℕ) (η : ℝ)
    (hband : ∀ S ⊆ P, ∀ k : ℕ, (∀ p ∈ S, index p = k) →
      ∑ p ∈ S, (p : ℝ)⁻¹ ≤ η) : 0 ≤ η := by
  simpa using hband ∅ (Finset.empty_subset P) 0 (by simp)

/-- Adjacent deletion gives a linear, rather than quadratic, length cost. -/
theorem reciprocal_mass_le (F : Finset (List ℕ)) (P : Finset ℕ)
    (index : ℕ → ℕ) (L : ℕ) (η : ℝ)
    (hstrict : ∀ t ∈ F, t.Pairwise (· > ·))
    (hpool : ∀ t ∈ F, ∀ p ∈ t, p ∈ P)
    (hlength : ∀ t ∈ F, t.length ≤ L)
    (hweak : ∀ t ∈ F, (t.map index).Pairwise (· ≥ ·))
    (hrepeat : ∀ t ∈ F, ¬(t.map index).Nodup)
    (hband : ∀ S ⊆ P, ∀ k : ℕ, (∀ p ∈ S, index p = k) →
      ∑ p ∈ S, (p : ℝ)⁻¹ ≤ η) :
    (∑ t ∈ F, SieveBoxMass.reciprocal t) ≤
      (L : ℝ) * η * ∏ p ∈ P, (1 + (p : ℝ)⁻¹) := by
  classical
  have hex : ∀ t ∈ F, ∃ j, 0 < j ∧ j < t.length ∧
      index (t[j - 1]!) = index (t[j]!) := by
    intro t ht
    exact adjacent_index_repeat index t (hweak t ht) (hrepeat t ht)
  let pos : List ℕ → ℕ := fun t =>
    if ht : t ∈ F then Classical.choose (hex t ht) else 0
  let mark : List ℕ → ℕ := fun t => t[pos t]!
  have hspec : ∀ t ∈ F, 0 < pos t ∧ pos t < t.length ∧
      index (t[pos t - 1]!) = index (mark t) := by
    intro t ht
    dsimp only [pos, mark]
    simpa only [dite_eq_left ht] using Classical.choose_spec (hex t ht)
  have hmark : ∀ t ∈ F, mark t ∈ t := by
    intro t ht
    dsimp only [mark]
    rw [getElem!_pos t (pos t) (hspec t ht).2.1]
    exact List.getElem_mem _
  apply SieveMarkedDeletion.reciprocal_mass_le F P mark pos L η
    hstrict hpool hmark (fun t ht => lt_of_lt_of_le (hspec t ht).2.1 (hlength t ht))
  intro i hi R _hRP
  let S := SieveMarkedDeletion.fiber F mark pos i R
  by_cases hS : S.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hS
    obtain ⟨v, hv, hvi, hvR, _hvp⟩ :=
      (SieveMarkedDeletion.mem_fiber F mark pos i R p₀).mp hp₀
    have hi0 : 0 < i := hvi ▸ (hspec v hv).1
    have hiv : i < v.length := hvi ▸ (hspec v hv).2.1
    apply hband S (k := index (v[i - 1]!))
    · intro p hp
      obtain ⟨t, ht, _hti, _htR, htp⟩ :=
        (SieveMarkedDeletion.mem_fiber F mark pos i R p).mp hp
      rw [← htp]
      exact hpool t ht (mark t) (hmark t ht)
    · intro p hp
      obtain ⟨t, ht, hti, htR, htp⟩ :=
        (SieveMarkedDeletion.mem_fiber F mark pos i R p).mp hp
      have hit : i < t.length := hti ▸ (hspec t ht).2.1
      have hmt : mark t = t[i] := by
        dsimp only [mark]
        rw [hti, getElem!_pos t i hit]
      have hmv : mark v = v[i] := by
        dsimp only [mark]
        rw [hvi, getElem!_pos v i hiv]
      have he := SieveMarkedDeletion.take_eq_of_residual_eq mark t v i
        (hstrict t ht) (hstrict v hv) hit hiv hmt hmv (htR.trans hvR.symm)
      have hpref := preceding_eq_of_take_eq t v i hi0 hit hiv he
      have hadj := (hspec t ht).2.2
      rw [hti] at hadj
      rw [← htp, ← hadj, hpref]
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (∑ p ∈ S, (p : ℝ)⁻¹) ≤ η
    rw [he, Finset.sum_empty]
    exact band_bound_nonneg P index η hband

/-- The coarser quadratic form is convenient for existing cutoff budgets. -/
theorem reciprocal_mass_le_square (F : Finset (List ℕ)) (P : Finset ℕ)
    (index : ℕ → ℕ) (L : ℕ) (η : ℝ)
    (hstrict : ∀ t ∈ F, t.Pairwise (· > ·))
    (hpool : ∀ t ∈ F, ∀ p ∈ t, p ∈ P)
    (hlength : ∀ t ∈ F, t.length ≤ L)
    (hweak : ∀ t ∈ F, (t.map index).Pairwise (· ≥ ·))
    (hrepeat : ∀ t ∈ F, ¬(t.map index).Nodup)
    (hband : ∀ S ⊆ P, ∀ k : ℕ, (∀ p ∈ S, index p = k) →
      ∑ p ∈ S, (p : ℝ)⁻¹ ≤ η) :
    (∑ t ∈ F, SieveBoxMass.reciprocal t) ≤
      (L : ℝ)^2 * η * ∏ p ∈ P, (1 + (p : ℝ)⁻¹) := by
  refine (reciprocal_mass_le F P index L η hstrict hpool hlength hweak hrepeat hband).trans ?_
  have hL : (L : ℝ) ≤ (L : ℝ)^2 := by
    exact_mod_cast (show L ≤ L ^ 2 from by simpa only [pow_two] using Nat.le_mul_self L)
  have hη := band_bound_nonneg P index η hband
  apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hη)
  exact Finset.prod_nonneg (fun p _ => by positivity)

run_cmd do
  for decl in [``adjacent_repeat, ``adjacent_index_repeat, ``preceding_eq_of_take_eq,
    ``band_bound_nonneg, ``reciprocal_mass_le, ``reciprocal_mass_le_square] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "REPEATED BAND DELETION: LINEAR LENGTH COST, STANDARD AXIOMS ONLY"

end SieveRepeatedBandDeletion
end
