import Mathlib.Tactic

/-! Generic soundness of finite prefix-sum certificates. This replaces repeated
literal rectangle summation by one checked chain of prefix increments. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace UpperProfileGridPrefix

def prefixCheck (q : ℕ → ℕ) : ℕ → List ℕ → Bool
  | _, [] => false
  | _, [_] => true
  | k, a::b::rest => decide (b=a+q k) && prefixCheck q (k+1) (b::rest)

theorem prefix_step (q : ℕ → ℕ) (p : List ℕ) (start j : ℕ)
    (hc : prefixCheck q start p = true) (hj : j+1 < p.length) :
    p[j+1]! = p[j]!+q (start+j) := by
  induction p generalizing start j with
  | nil => simp at hj
  | cons a p ih =>
    cases p with
    | nil => simp at hj
    | cons b rest =>
      simp only [prefixCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
      cases j with
      | zero => simpa using hc.1
      | succ j =>
        have h := ih (start+1) j hc.2 (by simpa using hj)
        simpa only [List.getElem!_cons_succ, Nat.add_assoc, Nat.add_comm 1] using h

theorem prefix_eq_sum (q : ℕ → ℕ) (p : List ℕ)
    (hc : prefixCheck q 0 p = true) (hz : p[0]! = 0)
    (n : ℕ) (hn : n < p.length) : p[n]! = ∑ k ∈ Finset.range n, q k := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    rw [prefix_step q p 0 n hc hn, ih (by omega), Finset.sum_range_succ]
    simp

theorem prefix_mono (q : ℕ → ℕ) (p : List ℕ)
    (hc : prefixCheck q 0 p = true) (hz : p[0]! = 0)
    (a k : ℕ) (hak : a ≤ k) (hk : k < p.length) : p[a]! ≤ p[k]! := by
  rw [prefix_eq_sum q p hc hz a (by omega), prefix_eq_sum q p hc hz k hk]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hak)

theorem prefix_sub_real (q : ℕ → ℕ) (p : List ℕ)
    (hc : prefixCheck q 0 p = true) (hz : p[0]! = 0)
    (a k : ℕ) (hak : a ≤ k) (hk : k < p.length) :
    ((p[k]!-p[a]! : ℕ) : ℝ) = ∑ n ∈ Finset.Ico a k, (q n : ℝ) := by
  rw [Nat.cast_sub (prefix_mono q p hc hz a k hak hk)]
  rw [prefix_eq_sum q p hc hz a (by omega), prefix_eq_sum q p hc hz k hk]
  push_cast
  exact (Finset.sum_Ico_eq_sub _ hak).symm

theorem split_sum (q : ℕ → ℝ) (a k : ℕ) (hak : a ≤ k) (A B C : ℝ) :
    (∑ n ∈ Finset.range k, if n<a then A*q n else B*q n-C) =
      A*(∑ n ∈ Finset.range a, q n) +
      B*((∑ n ∈ Finset.range k, q n)-(∑ n ∈ Finset.range a, q n))-
      ((k-a : ℕ) : ℝ)*C := by
  rw [← Finset.sum_range_add_sum_Ico _ hak]
  have ha : (∑ n ∈ Finset.range a, if n<a then A*q n else B*q n-C) =
      A*(∑ n ∈ Finset.range a, q n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [ite_eq_left (Finset.mem_range.mp hn)]
  have hb : (∑ n ∈ Finset.Ico a k, if n<a then A*q n else B*q n-C) =
      B*(∑ n ∈ Finset.Ico a k, q n)-((k-a : ℕ) : ℝ)*C := by
    simp only [Finset.mul_sum]
    rw [show ((k-a : ℕ) : ℝ)*C = ∑ _n ∈ Finset.Ico a k, C by simp]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [ite_eq_right (not_lt.mpr (Finset.mem_Ico.mp hn).1)]
  rw [ha, hb, Finset.sum_Ico_eq_sub _ hak]
  ring

theorem prefix_split_sum (q : ℕ → ℕ) (p : List ℕ)
    (hc : prefixCheck q 0 p = true) (hz : p[0]! = 0)
    (a k : ℕ) (hak : a ≤ k) (hk : k < p.length) (A B C : ℝ) :
    (∑ n ∈ Finset.range k, if n<a then A*(q n : ℝ) else B*(q n : ℝ)-C) =
      A*(p[a]! : ℝ)+B*((p[k]!-p[a]! : ℕ) : ℝ)-((k-a : ℕ) : ℝ)*C := by
  rw [split_sum _ a k hak A B C, Nat.cast_sub (prefix_mono q p hc hz a k hak hk),
    prefix_eq_sum q p hc hz a (by omega), prefix_eq_sum q p hc hz k hk]
  push_cast
  rfl

run_cmd do
  for decl in [``prefix_step, ``prefix_eq_sum, ``prefix_mono, ``prefix_sub_real,
      ``split_sum, ``prefix_split_sum] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "GENERIC EXACT PREFIX SUM CERTIFICATE SOUNDNESS"
end UpperProfileGridPrefix
