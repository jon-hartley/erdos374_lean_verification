import LogPhaseShape

/-!
Explicit dyadic logarithmic-phase bounds for the Dirichlet Gram kernel.
The first-difference estimate controls lengths above the frequency;
the second-difference estimate controls lengths below that scale.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set
open scoped BigOperators

namespace LogPhaseKernelBounds
open Erdos374.HigherDifference152 Erdos374.SecondDerivative151
open Erdos374.KusminLandau151 Erdos374.SecondDerivativeOptimized151
open LogPhaseShape

theorem first_difference_bound (N M : ℕ) (a u : ℝ)
    (hN : 1 ≤ N) (hM : M ≤ N) (ha : (N : ℝ) ≤ a)
    (haUpper : a ≤ 2 * N) (hu : 0 < u) (hsmall : 2 * u ≤ N) :
    ‖∑ n ∈ Finset.range M, Erdos374.KusminLandau151.e (phase u (a + n))‖ ≤ 8 * N / u := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hMr : (M : ℝ) ≤ N := by exact_mod_cast hM
  have hap : 0 < a := by linarith
  let δ := u / (a + M + 1)
  have hden : 0 < a + M + 1 := by positivity
  have hδ : 0 < δ := div_pos hu hden
  have hupper : u / a ≤ 1 / 2 := (div_le_iff₀ hap).mpr (by linarith)
  have hδUpper : δ ≤ u / a :=
    div_le_div_of_nonneg_left hu.le hap (by linarith [Nat.cast_nonneg (α := ℝ) M])
  have hh := kusmin_landau M (fun n => phase u (a + n)) δ hδ
    (hδUpper.trans hupper) (by
      intro n hn
      have hb := oriented_difference_bounds 0 M n a u hap hu.le hn
      simp only [Nat.zero_add, pow_zero, one_mul, Nat.factorial_zero,
        Nat.cast_one, pow_one] at hb
      change δ ≤ difference 1 (fun n => phase u (a + n)) n ∧
        difference 1 (fun n => phase u (a + n)) n ≤ 1 - δ
      exact ⟨hb.1, by linarith [hb.2]⟩) (by
      right
      have hm := oriented_difference_antitone 0 a u hap hu.le
      simp only [pow_zero, one_mul, Nat.zero_add] at hm
      exact fun _ _ _ _ hmn => hm hmn)
  apply hh.trans
  dsimp [δ]
  rw [div_div_eq_mul_div]
  apply (div_le_div_iff₀ hu hu).mpr
  nlinarith

theorem second_difference_bound (N M : ℕ) (a u : ℝ)
    (hN : 1 ≤ N) (hM : M ≤ N) (ha : (N : ℝ) ≤ a)
    (haUpper : a ≤ 2 * N) (hu : 0 < u) :
    ‖∑ n ∈ Finset.range M, Erdos374.KusminLandau151.e (phase u (a + n))‖ ^ 2 ≤
      20000 * (1 + Real.log ((N : ℝ) + 1)) *
        (u + (N : ℝ) ^ 2 / u) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hMr : (M : ℝ) ≤ N := by exact_mod_cast hM
  have hap : 0 < a := by linarith
  let L := u / (25 * (N : ℝ) ^ 2)
  have hL : 0 < L := by dsimp [L]; positivity
  have hshape : ∀ m < M,
      L ≤ secondDifference (fun n => phase (-u) (a + n)) m ∧
      secondDifference (fun n => phase (-u) (a + n)) m ≤ 25 * L := by
    intro m hm
    have hb := oriented_difference_bounds 1 M m a u hap hu.le hm
    simp only [Nat.one_add, pow_one, neg_mul, one_mul, Nat.factorial_one,
      Nat.cast_one, difference_two] at hb
    constructor
    · apply le_trans _ hb.1
      dsimp [L]
      apply div_le_div_of_nonneg_left hu.le (by positivity)
      have hr : a + M + 2 ≤ 5 * N := by linarith
      nlinarith [sq_nonneg (5 * (N : ℝ) - (a + M + 2))]
    · apply hb.2.trans
      calc
        u / a ^ 2 ≤ u / (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left hu.le (by positivity)
            (pow_le_pow_left₀ hNp.le ha 2)
        _ = 25 * L := by dsimp [L]; field_simp
  have hmono : Antitone (secondDifference (fun n => phase (-u) (a + n))) := by
    simpa only [pow_one, neg_mul, one_mul, Nat.one_add, difference_two] using
      oriented_difference_antitone 1 a u hap hu.le
  have hh := second_difference_optimized M (fun n => phase (-u) (a + n)) L 25
    hL (by norm_num) hshape (Or.inr (fun _ _ _ _ hmn => hmono hmn))
  rw [norm_sum_neg] at hh
  have hlog : 1 + Real.log ((M : ℝ) + 1) ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have hh := Real.log_le_log (by positivity : 0 < (M : ℝ) + 1)
      (show (M : ℝ) + 1 ≤ (N : ℝ) + 1 by linarith)
    linarith
  have hpiece : (M : ℝ) ^ 2 * L + 1 / L ≤ 25 * (u + (N : ℝ) ^ 2 / u) := by
    have hsq : (M : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hMr 2
    have hmul := mul_le_mul_of_nonneg_right hsq hL.le
    have hterm : (N : ℝ) ^ 2 * L = u / 25 := by dsimp [L]; field_simp
    have hinv : 1 / L = 25 * (N : ℝ) ^ 2 / u := by dsimp [L]; field_simp
    rw [hterm] at hmul
    calc
      _ ≤ u / 25 + 25 * (N : ℝ) ^ 2 / u := add_le_add hmul hinv.le
      _ ≤ _ := by rw [mul_div_assoc, mul_add]; linarith
  apply hh.trans
  have hG : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by
      linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith
  have hb := mul_le_mul
    (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 32 * 25))
    hpiece (by positivity) (by positivity)
  nlinarith

theorem combined_bound (N M : ℕ) (a u : ℝ)
    (hN : 1 ≤ N) (hM : M ≤ N) (ha : (N : ℝ) ≤ a)
    (haUpper : a ≤ 2 * N) (hu : 0 < u) :
    ‖∑ n ∈ Finset.range M, Erdos374.KusminLandau151.e (phase u (a + n))‖ ≤
      8 * N / u + 512 * Real.sqrt (u * (1 + Real.log ((N : ℝ) + 1))) := by
  have hG : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by
      linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith
  by_cases hsmall : 2 * u ≤ N
  · exact (first_difference_bound N M a u hN hM ha haUpper hu hsmall).trans
      (le_add_of_nonneg_right (by positivity))
  · have hh := second_difference_bound N M a u hN hM ha haUpper hu
    have hratio : (N : ℝ) ^ 2 / u ≤ 4 * u := by
      apply (div_le_iff₀ hu).mpr
      have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith [sq_nonneg (2 * u - (N : ℝ))]
    have hm := mul_le_mul_of_nonneg_left
      (show u + (N : ℝ) ^ 2 / u ≤ 5 * u by linarith)
      (show 0 ≤ 20000 * (1 + Real.log ((N : ℝ) + 1)) by positivity)
    have hsqrt :
        ‖∑ n ∈ Finset.range M, Erdos374.KusminLandau151.e (phase u (a + n))‖ ≤
          512 * Real.sqrt (u * (1 + Real.log ((N : ℝ) + 1))) := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hu.le hG)]
      nlinarith [mul_nonneg hu.le hG]
    exact hsqrt.trans (le_add_of_nonneg_left (by positivity))

theorem signed_bound (N M : ℕ) (a u : ℝ)
    (hN : 1 ≤ N) (hM : M ≤ N) (ha : (N : ℝ) ≤ a)
    (haUpper : a ≤ 2 * N) (hu : u ≠ 0) :
    ‖∑ n ∈ Finset.range M, Erdos374.KusminLandau151.e (phase u (a + n))‖ ≤
      8 * N / |u| + 512 * Real.sqrt (|u| * (1 + Real.log ((N : ℝ) + 1))) := by
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · have hh := combined_bound N M a (-u) hN hM ha haUpper (by linarith)
    rw [norm_sum_neg] at hh
    simpa only [abs_of_neg hneg] using hh
  · simpa only [abs_of_pos hpos] using combined_bound N M a u hN hM ha haUpper hpos

end LogPhaseKernelBounds

#print axioms LogPhaseKernelBounds.first_difference_bound
#print axioms LogPhaseKernelBounds.second_difference_bound
#print axioms LogPhaseKernelBounds.signed_bound
run_cmd do
  for target in [``LogPhaseKernelBounds.first_difference_bound,
      ``LogPhaseKernelBounds.second_difference_bound,
      ``LogPhaseKernelBounds.signed_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "LOG PHASE KERNEL BOUNDS PASSED"
