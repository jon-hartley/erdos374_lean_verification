import CheckedSamplingFourierVaughanBands

/-!
Exact powers-of-two partition and Vaughan cutoffs for Type II aggregation.
The cutoffs are chosen before the coefficients or interval endpoint.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace DyadicVaughan
open Erdos374.Vaughan145 Erdos374.BilinearCorrelation152
open Erdos374.ReciprocalCharacter151

def cutoffExponent (P : ℕ) : ℕ := Nat.log 2 P / 3
def cutoff (P : ℕ) : ℕ := 2 ^ cutoffExponent P
def bandCount (P : ℕ) : ℕ := Nat.log 2 (2 * P) + 1

theorem cutoff_properties (P : ℕ) (hP : 512 ≤ P) :
    8 ≤ cutoff P ∧ cutoff P ≤ P ∧ cutoff P ^ 3 ≤ P ∧ P ≤ cutoff P ^ 4 := by
  have hP0 : P ≠ 0 := by omega
  have hlog9 : 9 ≤ Nat.log 2 P :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by norm_num; omega)
  have hq3 : 3 ≤ cutoffExponent P := by unfold cutoffExponent; omega
  have hU8 : 8 ≤ cutoff P := by
    simpa only [cutoff, show (8 : ℕ) = 2 ^ 3 by norm_num] using
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hq3
  have hpower := Nat.pow_log_le_self 2 hP0
  have hUle : cutoff P ≤ P := by
    apply (Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.div_le_self (Nat.log 2 P) 3)).trans hpower
  have hcube : cutoff P ^ 3 ≤ P := by
    unfold cutoff
    rw [← pow_mul]
    apply (Nat.pow_le_pow_right (by norm_num : 0 < 2) ?_).trans hpower
    unfold cutoffExponent
    omega
  have hPupper : P < 8 * cutoff P ^ 3 := by
    have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) P
    have hindex : Nat.log 2 P + 1 ≤ cutoffExponent P * 3 + 3 := by
      unfold cutoffExponent
      omega
    have hp := hh.trans_le (Nat.pow_le_pow_right (by norm_num : 0 < 2) hindex)
    simpa only [cutoff, pow_add, pow_mul, show (2 : ℕ) ^ 3 = 8 by norm_num,
      Nat.mul_comm] using hp
  refine ⟨hU8, hUle, hcube, ?_⟩
  calc
    P ≤ 8 * cutoff P ^ 3 := hPupper.le
    _ ≤ cutoff P * cutoff P ^ 3 := Nat.mul_le_mul_right _ hU8
    _ = cutoff P ^ 4 := by ring

theorem band_count_covers (P : ℕ) : 2 * P ≤ 2 ^ bandCount P :=
  (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (2 * P)).le

theorem sum_dyadic_intervals (L : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ Finset.range L, ∑ d ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f d) =
      ∑ d ∈ Finset.Ioc 1 (2 ^ L), f d := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    exact Finset.sum_Ioc_consecutive f (one_le_pow₀ (by norm_num))
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega))

theorem double_sum_dyadic_intervals (L : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ j ∈ Finset.range L, ∑ h ∈ Finset.range L,
      ∑ d ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)),
        ∑ k ∈ Finset.Ioc (2 ^ h) (2 ^ (h + 1)), f d k) =
      ∑ d ∈ Finset.Ioc 1 (2 ^ L), ∑ k ∈ Finset.Ioc 1 (2 ^ L), f d k := by
  trans ∑ j ∈ Finset.range L, ∑ d ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)),
    ∑ k ∈ Finset.Ioc 1 (2 ^ L), f d k
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    exact sum_dyadic_intervals L (f d)
  · exact sum_dyadic_intervals L _

theorem band_count_le_log (P : ℕ) (hP : 2 ≤ P) (hlog : 1 ≤ Real.log (P : ℝ)) :
    (bandCount P : ℝ) ≤ 5 * Real.log (P : ℝ) := by
  have htwoP : (0 : ℝ) < 2 * (P : ℝ) := by positivity
  have hpow : (2 : ℝ) ^ Nat.log 2 (2 * P) ≤ 2 * (P : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (show 2 * P ≠ 0 by omega)
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 (2 * P)) hpow
  rw [Real.log_pow] at hl
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have hPtwo : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hlogtwo : Real.log (2 * (P : ℝ)) ≤ 2 * Real.log (P : ℝ) := by
    have hh := Real.log_le_log htwoP (show 2 * (P : ℝ) ≤ (P : ℝ) ^ 2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hh := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (Nat.log 2 (2 * P)) : (0 : ℝ) ≤ _)
  unfold bandCount
  push_cast
  nlinarith only [hl, hlogtwo, hh, hlog]

end DyadicVaughan

#print axioms DyadicVaughan.cutoff_properties
#print axioms DyadicVaughan.double_sum_dyadic_intervals
run_cmd do
  for target in [``DyadicVaughan.cutoff_properties,
      ``DyadicVaughan.double_sum_dyadic_intervals, ``DyadicVaughan.band_count_le_log] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "DYADIC VAUGHAN PASSED"

run_cmd do
  for target in [``DyadicVaughan.cutoff_properties,
      ``DyadicVaughan.band_count_covers,
      ``DyadicVaughan.sum_dyadic_intervals,
      ``DyadicVaughan.double_sum_dyadic_intervals,
      ``DyadicVaughan.band_count_le_log] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
