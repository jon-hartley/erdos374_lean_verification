import LogPhaseShape

/-!
First-difference cancellation for logarithmic phases at frequencies
below the length scale. This covers the range left below the fixed
power threshold in LogPhaseCancellation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set
open scoped BigOperators

namespace LogPhaseFirstDifference
open Erdos374.HigherDifference152 Erdos374.KusminLandau151
open LogPhaseShape

theorem positive_bound (N M : ℕ) (a u : ℝ) (hN : 1 ≤ N) (hM : M ≤ N)
    (ha : (N : ℝ) ≤ a) (haUpper : a ≤ 2 * (N : ℝ))
    (hu : 0 < u) (huUpper : u ≤ (N : ℝ) / 4) :
    ‖∑ n ∈ Finset.range M, Erdos374.KusminLandau151.e (phase u (a + n))‖ ≤ 8 * (N : ℝ) / u := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hap : 0 < a := hNp.trans_le ha
  let δ := u / (4 * (N : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * (N : ℝ))).mpr
    linarith
  have hupper : u / a ≤ 1 / 4 := by
    apply (div_le_iff₀ hap).mpr
    linarith
  have hd : ∀ n < M, δ ≤ phase u (a + (n + 1 : ℕ)) - phase u (a + n) ∧
      phase u (a + (n + 1 : ℕ)) - phase u (a + n) ≤ 1 - δ := by
    intro n hn
    have hb := oriented_difference_bounds 0 N n a u hap hu.le (hn.trans_le hM)
    norm_num only [Nat.zero_add, Nat.factorial_zero, Nat.cast_one, pow_one, pow_zero,
      one_mul, difference] at hb
    have hden : a + (N : ℝ) + 1 ≤ 4 * (N : ℝ) := by linarith
    have hlow : δ ≤ u / (a + (N : ℝ) + 1) :=
      div_le_div_of_nonneg_left hu.le (by positivity) hden
    exact ⟨hlow.trans hb.1, hb.2.trans (by linarith)⟩
  have hm : Antitone (fun n : ℕ => phase u (a + (n + 1 : ℕ)) - phase u (a + n)) := by
    have hh := oriented_difference_antitone 0 a u hap hu.le
    norm_num only [pow_zero, one_mul] at hh
    exact hh
  have hh := kusmin_landau M (fun n => phase u (a + n)) δ hδ
    (by linarith) hd (Or.inr (hm.antitoneOn _))
  apply hh.trans_eq
  dsimp [δ]
  field_simp
  norm_num

theorem signed_bound (N M : ℕ) (a u : ℝ) (hN : 1 ≤ N) (hM : M ≤ N)
    (ha : (N : ℝ) ≤ a) (haUpper : a ≤ 2 * (N : ℝ))
    (hu : 0 < |u|) (huUpper : |u| ≤ (N : ℝ) / 4) :
    ‖∑ n ∈ Finset.range M, Erdos374.KusminLandau151.e (phase u (a + n))‖ ≤ 8 * (N : ℝ) / |u| := by
  by_cases hu0 : 0 ≤ u
  · rw [abs_of_nonneg hu0] at hu huUpper ⊢
    exact positive_bound N M a u hN hM ha haUpper hu huUpper
  · have heq : u = -|u| := by rw [abs_of_neg (lt_of_not_ge hu0)]; ring
    conv_lhs => rw [heq]
    rw [norm_sum_neg]
    exact positive_bound N M a |u| hN hM ha haUpper hu huUpper

end LogPhaseFirstDifference

#print axioms LogPhaseFirstDifference.signed_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``LogPhaseFirstDifference.signed_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "LOG PHASE FIRST DIFFERENCE PASSED"
