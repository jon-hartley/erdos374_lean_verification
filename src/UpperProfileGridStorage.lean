import UpperProfileGridPrefix

/-! Balanced exact integer storage. No correctness of a generated tree is
assumed: its lookup function must pass the complete increment certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace UpperProfileGridStorage

inductive Tree where
  | leaf : ℕ → Tree
  | node : ℕ → Tree → Tree → Tree
deriving Inhabited

def lookup : Tree → ℕ → ℕ
  | .leaf a, _ => a
  | .node leftSize l r, k =>
      if k < leftSize then lookup l k else lookup r (k-leftSize)

def increments (q p : ℕ → ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | start, n+1 => decide (p (start+1)=p start+q start) &&
      increments q p (start+1) n

theorem increments_step (q p : ℕ → ℕ) (start N j : ℕ)
    (hc : increments q p start N = true) (hj : j < N) :
    p (start+j+1) = p (start+j)+q (start+j) := by
  induction N generalizing start j with
  | zero => omega
  | succ N ih =>
    simp only [increments, Bool.and_eq_true, decide_eq_true_eq] at hc
    cases j with
    | zero => simpa using hc.1
    | succ j =>
      have h := ih (start+1) j hc.2 (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1] using h

theorem increments_prefix (q p : ℕ → ℕ) (N : ℕ)
    (hc : increments q p 0 N = true) (hz : p 0=0)
    (n : ℕ) (hn : n ≤ N) : p n = ∑ k ∈ Finset.range n, q k := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    have h := increments_step q p 0 N n hc (by omega)
    simpa only [Nat.zero_add, Finset.sum_range_succ, ih (by omega)] using h

theorem increments_mono (q p : ℕ → ℕ) (N : ℕ)
    (hc : increments q p 0 N = true) (hz : p 0=0)
    (a k : ℕ) (hak : a ≤ k) (hk : k ≤ N) : p a ≤ p k := by
  rw [increments_prefix q p N hc hz a (by omega), increments_prefix q p N hc hz k hk]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hak)

theorem increments_split (q p : ℕ → ℕ) (N : ℕ)
    (hc : increments q p 0 N = true) (hz : p 0=0)
    (a k : ℕ) (hak : a ≤ k) (hk : k ≤ N) (A B C : ℝ) :
    (∑ n ∈ Finset.range k, if n<a then A*(q n : ℝ) else B*(q n : ℝ)-C) =
      A*(p a : ℝ)+B*((p k-p a : ℕ) : ℝ)-((k-a : ℕ) : ℝ)*C := by
  rw [UpperProfileGridPrefix.split_sum _ a k hak A B C,
    Nat.cast_sub (increments_mono q p N hc hz a k hak hk),
    increments_prefix q p N hc hz a (by omega), increments_prefix q p N hc hz k hk]
  push_cast
  rfl

run_cmd do
  for decl in [``increments_step, ``increments_prefix, ``increments_mono,
      ``increments_split] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "BALANCED PREFIX LOOKUP CERTIFICATE SOUNDNESS"
end UpperProfileGridStorage
