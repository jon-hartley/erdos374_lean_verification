import OuterPairActualIntervalWork

/-! Restrict a constant-weight prime interval by an order-convex predicate.
The resulting coefficient still has interval support and retains its unit cap. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable

namespace OuterPrimeIntervalRestrictionWork

theorem restrict_weighted_interval (P : Finset ℕ) (f : ℕ → ℂ)
    (Q : ℕ → Prop)
    (hconv : ∀ p∈P, ∀ q∈P, ∀ r∈P, p≤q → q≤r → Q p → Q r → Q q)
    (hcap : ∀ p∈P, ‖f p‖≤1)
    (hinterval : ∃ lo hi : ℕ, ∃ c : ℂ, ∀ p∈P,
      f p = if lo≤p ∧ p≤hi then c else 0) :
    ∃ lo hi : ℕ, ∃ c : ℂ, ‖c‖≤1 ∧ ∀ p∈P,
      (if Q p then f p else 0) = if lo≤p ∧ p≤hi then c else 0 := by
  obtain ⟨lo,hi,c,hrep⟩ := hinterval
  let F := P.filter (fun p => lo≤p ∧ p≤hi ∧ Q p)
  by_cases hF : F.Nonempty
  · let l := F.min' hF
    let h := F.max' hF
    have hl := Finset.mem_filter.mp (Finset.min'_mem F hF)
    have hh := Finset.mem_filter.mp (Finset.max'_mem F hF)
    have hc : ‖c‖≤1 := by
      have he := hrep l hl.1
      rw [ite_eq_left ⟨hl.2.1,hl.2.2.1⟩] at he
      simpa only [he] using hcap l hl.1
    have hmem (p : ℕ) (hp : p∈P) :
        (lo≤p ∧ p≤hi ∧ Q p) ↔ l≤p ∧ p≤h := by
      constructor
      · intro hf
        have hpF : p∈F := Finset.mem_filter.mpr ⟨hp,hf⟩
        exact ⟨Finset.min'_le F p hpF,Finset.le_max' F p hpF⟩
      · rintro ⟨hlp,hph⟩
        exact ⟨hl.2.1.trans hlp,hph.trans hh.2.2.1,
          hconv l hl.1 p hp h hh.1 hlp hph hl.2.2.2 hh.2.2.2⟩
    refine ⟨l,h,c,hc,?_⟩
    intro p hp
    simp only [hrep p hp,←hmem p hp]
    by_cases hQ : Q p <;> by_cases hlo : lo≤p <;>
      by_cases hhi : p≤hi <;> simp [hQ,hlo,hhi]
  · refine ⟨1,0,0,by simp,?_⟩
    intro p hp
    have hn : ¬(lo≤p ∧ p≤hi ∧ Q p) := by
      intro hh
      exact hF ⟨p,Finset.mem_filter.mpr ⟨hp,hh⟩⟩
    rw [hrep p hp]
    by_cases hQ : Q p <;> by_cases hlo : lo≤p <;>
      by_cases hhi : p≤hi <;> simp_all

run_cmd do
  for decl in [``restrict_weighted_interval] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPrimeIntervalRestrictionWork
