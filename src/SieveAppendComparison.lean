import SievePrefixLoss

/-! Exact one-sided comparison after replacing an appended tail by its
Euler factor. Both selector states are proved together; skipped gates retain
their state and accumulator. The no-duplicate premise is essential. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
attribute [local instance] Classical.propDecidable

namespace SieveAppendComparison
open SievePrefix SievePrefixLoss

theorem value_append_bounds (gate : ℕ → ℕ → Prop) (d : ℕ)
    (ps qs : List ℕ) (b : ℕ → ℝ) (hnd : (ps++qs).Nodup)
    (hb : ∀ p ∈ ps++qs, 0 ≤ b p ∧ b p ≤ 1) :
    value gate false d (ps++qs) b ≤ euler qs b*value gate false d ps b ∧
      euler qs b*value gate true d ps b ≤ value gate true d (ps++qs) b := by
  induction ps generalizing d with
  | nil =>
    have hh := value_bounds gate d qs b (by simpa using hnd) (by simpa using hb)
    simpa only [List.nil_append, euler, value, selected, Finset.sum_singleton,
      term, Finset.card_empty, pow_zero, Finset.prod_empty, mul_one] using hh
  | cons p ps ih =>
    have hn : (p::(ps++qs)).Nodup := by simpa only [List.cons_append] using hnd
    obtain ⟨hp, htail⟩ := List.nodup_cons.mp hn
    have hpps : p ∉ ps := fun h => hp (List.mem_append_left qs h)
    have hb' : ∀ q ∈ ps++qs, 0 ≤ b q ∧ b q ≤ 1 := by
      intro q hq
      exact hb q (by simpa only [List.cons_append, List.mem_cons] using Or.inr hq)
    have hbp : 0 ≤ b p := (hb p (by simp)).1
    have hskip := ih d htail hb'
    have htake := ih (d*p) htail hb'
    simp only [List.cons_append]
    rw [value_cons gate false d p (ps++qs) b hp,
      value_cons gate true d p (ps++qs) b hp,
      value_cons gate false d p ps b hpps, value_cons gate true d p ps b hpps]
    simp only [Bool.not_false, Bool.not_true, Bool.true_eq_false, false_or, true_or, ite_true]
    constructor
    · calc
        _ ≤ euler qs b*value gate false d ps b - b p*(euler qs b*value gate true (d*p) ps b) :=
          sub_le_sub hskip.1 (mul_le_mul_of_nonneg_left htake.2 hbp)
        _ = _ := by ring
    · by_cases hg : gate d p
      · simp only [hg, ite_true]
        calc
          _ = euler qs b*value gate true d ps b - b p*(euler qs b*value gate false (d*p) ps b) := by ring
          _ ≤ _ := sub_le_sub hskip.2 (mul_le_mul_of_nonneg_left htake.1 hbp)
      · simpa only [hg, ite_false, sub_zero] using hskip.2

theorem lower_append_le (gate : ℕ → ℕ → Prop) (d : ℕ)
    (ps qs : List ℕ) (b : ℕ → ℝ) (hnd : (ps++qs).Nodup)
    (hb : ∀ p ∈ ps++qs, 0 ≤ b p ∧ b p ≤ 1) :
    value gate false d (ps++qs) b ≤ euler qs b*value gate false d ps b :=
  (value_append_bounds gate d ps qs b hnd hb).1

theorem upper_append_le (gate : ℕ → ℕ → Prop) (d : ℕ)
    (ps qs : List ℕ) (b : ℕ → ℝ) (hnd : (ps++qs).Nodup)
    (hb : ∀ p ∈ ps++qs, 0 ≤ b p ∧ b p ≤ 1) :
    euler qs b*value gate true d ps b ≤ value gate true d (ps++qs) b :=
  (value_append_bounds gate d ps qs b hnd hb).2

run_cmd do
  for decl in [``value_append_bounds, ``lower_append_le, ``upper_append_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT SIMULTANEOUS SELECTOR APPEND INEQUALITIES PASSED"
end SieveAppendComparison
end
