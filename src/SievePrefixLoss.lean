import SievePrefix

/-! Exact nonnegative losses of the constructed finite selectors. These
identities expose the stopping losses; they do not estimate them asymptotically. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SievePrefixLoss

def euler (ps : List ℕ) (b : ℕ → ℝ) : ℝ := ∏ p ∈ ps.toFinset, (1 - b p)

def lower (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ) (b : ℕ → ℝ) : ℝ :=
  euler ps b - SievePrefix.value gate false d ps b

def upper (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ) (b : ℕ → ℝ) : ℝ :=
  SievePrefix.value gate true d ps b - euler ps b

theorem euler_cons (p : ℕ) (ps : List ℕ) (b : ℕ → ℝ) (hp : p ∉ ps) :
    euler (p :: ps) b = (1 - b p) * euler ps b := by
  simp [euler, hp]

theorem nonnegative (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (b : ℕ → ℝ) (hnd : ps.Nodup) (hb : ∀ p ∈ ps, 0 ≤ b p ∧ b p ≤ 1) :
    0 ≤ lower gate d ps b ∧ 0 ≤ upper gate d ps b := by
  obtain ⟨hl, hu⟩ := SievePrefix.value_bounds gate d ps b hnd hb
  exact ⟨sub_nonneg.mpr hl, sub_nonneg.mpr hu⟩

theorem lower_cons (gate : ℕ → ℕ → Prop) (d p : ℕ) (ps : List ℕ)
    (b : ℕ → ℝ) (hp : p ∉ ps) :
    lower gate d (p :: ps) b = lower gate d ps b + b p * upper gate (d*p) ps b := by
  unfold lower upper
  rw [euler_cons p ps b hp, SievePrefix.value_cons gate false d p ps b hp]
  simp only [Bool.not_false, true_or, ite_true]
  ring

theorem upper_cons (gate : ℕ → ℕ → Prop) (d p : ℕ) (ps : List ℕ)
    (b : ℕ → ℝ) (hp : p ∉ ps) :
    upper gate d (p :: ps) b = upper gate d ps b +
      if gate d p then b p * lower gate (d*p) ps b else b p * euler ps b := by
  classical
  unfold lower upper
  rw [euler_cons p ps b hp, SievePrefix.value_cons gate true d p ps b hp]
  simp only [Bool.not_true, Bool.true_eq_false, false_or]
  split_ifs <;> ring

theorem nil_losses (gate : ℕ → ℕ → Prop) (d : ℕ) (b : ℕ → ℝ) :
    lower gate d [] b = 0 ∧ upper gate d [] b = 0 := by
  simp [lower, upper, euler, SievePrefix.value, SievePrefix.selected, SievePrefix.term]

/-- With every gate open the recursive selector has no stopping loss. -/
theorem open_gate_exact (d : ℕ) (ps : List ℕ) (b : ℕ → ℝ) (hnd : ps.Nodup) :
    lower (fun _ _ => True) d ps b = 0 ∧ upper (fun _ _ => True) d ps b = 0 := by
  induction ps generalizing d with
  | nil => exact nil_losses _ d b
  | cons p ps ih =>
    obtain ⟨hp, hnd⟩ := List.nodup_cons.mp hnd
    rw [lower_cons _ d p ps b hp, upper_cons _ d p ps b hp]
    simp [(ih d hnd).1, (ih d hnd).2, (ih (d*p) hnd).1, (ih (d*p) hnd).2]

run_cmd do
  for decl in [``euler_cons, ``nonnegative, ``lower_cons, ``upper_cons,
      ``nil_losses, ``open_gate_exact] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SIEVE PREFIX LOSS RECURRENCES PASSED"

end SievePrefixLoss
end
