import FiniteSieveWindow

/-! Exact passage from finite divisor evaluations to interval counts.
The lower endpoint is excluded. Signed coefficients and their multiplicities
are preserved. These are finite identities and comparison lemmas; the actual
selector construction is attached in a separate module. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace SieveDivisorWindow
open Erdos374.HarmanAnalytic151

/-- The pointwise finite divisor evaluation, with arbitrary signed weights. -/
def evaluation (s : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ s, if d ∣ n then w d else 0

def avoids (P : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ P, ¬ p ∣ n

def indicator (P : Finset ℕ) (n : ℕ) : ℝ := by
  classical
  exact if avoids P n then 1 else 0

def siftedWindow (P : Finset ℕ) (L R : ℝ) : Finset ℕ := by
  classical
  exact (FiniteSieveWindow.window L R).filter (avoids P)

theorem mem_window_iff (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) (n : ℕ) :
    n ∈ FiniteSieveWindow.window L R ↔ L < (n : ℝ) ∧ (n : ℝ) ≤ R := by
  simp only [FiniteSieveWindow.window, Finset.mem_Ioc,
    Nat.floor_lt hL, Nat.le_floor_iff (hL.trans hLR)]

theorem window_positive (L R : ℝ) (n : ℕ)
    (hn : n ∈ FiniteSieveWindow.window L R) : 0 < n := by
  have hh := (Finset.mem_Ioc.mp hn).1
  omega

theorem sum_evaluation_eq_divisorCount (s : Finset ℕ) (w : ℕ → ℝ)
    (L R : ℝ) (hs : ∀ d ∈ s, 0 < d) (hL : 0 ≤ L) (hLR : L ≤ R) :
    (∑ n ∈ FiniteSieveWindow.window L R, evaluation s w n) =
      HarmanDivisorWindow.divisorCount s w L R := by
  classical
  unfold evaluation HarmanDivisorWindow.divisorCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hcard := FiniteSieveWindow.divisorSlice_card_eq_divisorCount L R d hL hLR (hs d hd)
  have hsum : (∑ n ∈ FiniteSieveWindow.window L R, if d ∣ n then w d else 0) =
      ((divisorSlice (FiniteSieveWindow.window L R) d).card : ℝ) * w d := by
    simp only [divisorSlice, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hsum, hcard]
  simp only [HarmanDivisorWindow.divisorCount, Finset.sum_singleton, one_mul]
  ring

theorem divisorCount_eq_main_add_remainder (s : Finset ℕ) (w : ℕ → ℝ)
    (L R : ℝ) :
    HarmanDivisorWindow.divisorCount s w L R =
      (R - L) * HarmanDivisorWindow.reciprocalMass s w +
        HarmanDivisorWindow.remainder s w L R := by
  unfold HarmanDivisorWindow.remainder
  ring

theorem sum_evaluation_eq_main_add_remainder (s : Finset ℕ) (w : ℕ → ℝ)
    (L R : ℝ) (hs : ∀ d ∈ s, 0 < d) (hL : 0 ≤ L) (hLR : L ≤ R) :
    (∑ n ∈ FiniteSieveWindow.window L R, evaluation s w n) =
      (R - L) * HarmanDivisorWindow.reciprocalMass s w +
        HarmanDivisorWindow.remainder s w L R := by
  rw [sum_evaluation_eq_divisorCount s w L R hs hL hLR,
    divisorCount_eq_main_add_remainder]

theorem sum_indicator_eq_card (P : Finset ℕ) (L R : ℝ) :
    (∑ n ∈ FiniteSieveWindow.window L R, indicator P n) =
      ((siftedWindow P L R).card : ℝ) := by
  classical
  simp [indicator, siftedWindow, Finset.sum_boole]

theorem indicator_eq_product (P : Finset ℕ) (n : ℕ) :
    indicator P n = ∏ p ∈ P, (1 - if p ∣ n then (1 : ℝ) else 0) := by
  classical
  by_cases h : avoids P n
  · rw [indicator, ite_eq_left h]
    symm
    apply Finset.prod_eq_one
    intro p hp
    simp [h p hp]
  · rw [indicator, ite_eq_right h]
    simp only [avoids, not_forall, not_not] at h
    obtain ⟨p, hp, hpn⟩ := h
    symm
    exact Finset.prod_eq_zero hp (by simp [hpn])

/-- Generic comparison layer; the final selector adapter supplies these pointwise inequalities. -/
theorem count_bounds_of_pointwise (P sLow sUp : Finset ℕ) (wLow wUp : ℕ → ℝ)
    (L R : ℝ) (hLow : ∀ d ∈ sLow, 0 < d) (hUp : ∀ d ∈ sUp, 0 < d)
    (hL : 0 ≤ L) (hLR : L ≤ R)
    (hpoint : ∀ n ∈ FiniteSieveWindow.window L R,
      evaluation sLow wLow n ≤ indicator P n ∧ indicator P n ≤ evaluation sUp wUp n) :
    HarmanDivisorWindow.divisorCount sLow wLow L R ≤ ((siftedWindow P L R).card : ℝ) ∧
      ((siftedWindow P L R).card : ℝ) ≤ HarmanDivisorWindow.divisorCount sUp wUp L R := by
  rw [← sum_evaluation_eq_divisorCount sLow wLow L R hLow hL hLR,
    ← sum_evaluation_eq_divisorCount sUp wUp L R hUp hL hLR,
    ← sum_indicator_eq_card]
  exact ⟨Finset.sum_le_sum (fun n hn => (hpoint n hn).1),
    Finset.sum_le_sum (fun n hn => (hpoint n hn).2)⟩

theorem main_remainder_bounds_of_pointwise (P sLow sUp : Finset ℕ)
    (wLow wUp : ℕ → ℝ) (L R : ℝ)
    (hLow : ∀ d ∈ sLow, 0 < d) (hUp : ∀ d ∈ sUp, 0 < d)
    (hL : 0 ≤ L) (hLR : L ≤ R)
    (hpoint : ∀ n ∈ FiniteSieveWindow.window L R,
      evaluation sLow wLow n ≤ indicator P n ∧ indicator P n ≤ evaluation sUp wUp n) :
    (R - L) * HarmanDivisorWindow.reciprocalMass sLow wLow +
        HarmanDivisorWindow.remainder sLow wLow L R ≤ ((siftedWindow P L R).card : ℝ) ∧
      ((siftedWindow P L R).card : ℝ) ≤
        (R - L) * HarmanDivisorWindow.reciprocalMass sUp wUp +
          HarmanDivisorWindow.remainder sUp wUp L R := by
  simpa only [divisorCount_eq_main_add_remainder] using
    count_bounds_of_pointwise P sLow sUp wLow wUp L R hLow hUp hL hLR hpoint

theorem avoids_primeBand_iff_rough (z n : ℕ) :
    avoids (primeBand 0 z) n ↔ Rough z n := by
  simp only [avoids, primeBand, Rough, Finset.mem_filter, Finset.mem_Ico, Nat.zero_le, true_and, and_imp]
  constructor
  · intro h p hp hz
    exact h p hz hp
  · intro h p hz hp
    exact h p hp hz

theorem siftedWindow_primeBand (z : ℕ) (L R : ℝ) :
    siftedWindow (primeBand 0 z) L R = sifted (FiniteSieveWindow.window L R) z := by
  classical
  ext n
  simp [siftedWindow, sifted, avoids_primeBand_iff_rough]

theorem siftedWindow_top_eq_primeWindow (L R : ℝ)
    (hL : 1 ≤ L) (hLR : L ≤ R) (hsqrt : Nat.sqrt ⌊R⌋₊ ≤ ⌊L⌋₊) :
    siftedWindow (primeBand 0 (FiniteSieveWindow.topCutoff R)) L R =
      FiniteSieveWindow.primeWindow L R := by
  rw [siftedWindow_primeBand]
  exact FiniteSieveWindow.sifted_top_eq_primeWindow L R hL hLR hsqrt

end SieveDivisorWindow

run_cmd do
  for target in [``SieveDivisorWindow.mem_window_iff, ``SieveDivisorWindow.window_positive,
      ``SieveDivisorWindow.sum_evaluation_eq_divisorCount,
      ``SieveDivisorWindow.divisorCount_eq_main_add_remainder,
      ``SieveDivisorWindow.sum_evaluation_eq_main_add_remainder,
      ``SieveDivisorWindow.sum_indicator_eq_card, ``SieveDivisorWindow.indicator_eq_product,
      ``SieveDivisorWindow.count_bounds_of_pointwise,
      ``SieveDivisorWindow.main_remainder_bounds_of_pointwise,
      ``SieveDivisorWindow.avoids_primeBand_iff_rough,
      ``SieveDivisorWindow.siftedWindow_primeBand,
      ``SieveDivisorWindow.siftedWindow_top_eq_primeWindow] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "SIEVE DIVISOR WINDOW EXACT BRIDGE PASSED"

end
