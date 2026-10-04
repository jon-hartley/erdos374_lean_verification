import SieveSelectedWindow
import SieveFullCutoffTransfer

/-! Exact actual upper-selector bounds for sifted and prime windows.
The signed divisor remainder is retained literally; no estimate for it
is an input or a conclusion of this finite adapter. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace SieveUpperSelectedWindow

def remainder (T z L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder (SieveSmallWeights.support T z true)
    (SieveSmallWeights.weight T z true) L R

theorem reciprocalMass_eq_fullUpper (T z : ℝ) :
    HarmanDivisorWindow.reciprocalMass (SieveSmallWeights.support T z true)
      (SieveSmallWeights.weight T z true) = SieveFullCutoffTransfer.fullUpper T z := by
  rw [SieveFullCutoffTransfer.fullUpper_eq_mass]
  rfl

/-- Literal signed floor error over the actual collected upper weights. -/
theorem remainder_eq_sum (T z L R : ℝ) :
    remainder T z L R =
      ∑ d ∈ SieveSmallWeights.support T z true,
        SieveSmallWeights.weight T z true d *
          (((⌊R / d⌋₊ : ℝ) - (⌊L / d⌋₊ : ℝ)) - (R-L)/d) := by
  unfold remainder HarmanDivisorWindow.remainder HarmanDivisorWindow.divisorCount
    HarmanDivisorWindow.reciprocalMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem sifted_count_le (T z L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) :
    ((SieveDivisorWindow.siftedWindow (SieveSmallWeights.pool z) L R).card : ℝ) ≤
      (R-L)*SieveFullCutoffTransfer.fullUpper T z + remainder T z L R := by
  have h := (SieveSelectedWindow.main_remainder_bounds (SieveRosser.cubicGate T)
    1 (SieveSmallWeights.primes z) (SieveSmallWeights.primes_nodup z)
    (SieveSmallWeights.primes_prime z) L R hL hLR).2
  rw [SieveSmallWeights.primes_toFinset] at h
  change ((SieveDivisorWindow.siftedWindow (SieveSmallWeights.pool z) L R).card : ℝ) ≤
    (R-L)*HarmanDivisorWindow.reciprocalMass (SieveSmallWeights.support T z true)
      (SieveSmallWeights.weight T z true) + remainder T z L R at h
  simpa only [reciprocalMass_eq_fullUpper] using h

/-- Every prime in the open-left window exceeds every sieving prime.
No square-root cutoff equality is needed for this upper comparison. -/
theorem primeWindow_subset_sifted (z L R : ℝ)
    (hL : 0 ≤ L) (hLR : L ≤ R) (hzL : z ≤ L) :
    FiniteSieveWindow.primeWindow L R ⊆
      SieveDivisorWindow.siftedWindow (SieveSmallWeights.pool z) L R := by
  classical
  intro n hn
  obtain ⟨hnw, hnp⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hnw, ?_⟩
  intro p hp hpn
  obtain ⟨hpp, hpz⟩ := (SieveSmallWeights.mem_pool z p).mp hp
  have hpn' : p = n := (Nat.prime_dvd_prime_iff_eq hpp hnp).mp hpn
  have hLn := ((SieveDivisorWindow.mem_window_iff L R hL hLR n).mp hnw).1
  subst p
  linarith

theorem prime_count_le (T z L R : ℝ)
    (hL : 0 ≤ L) (hLR : L ≤ R) (hzL : z ≤ L) :
    ((FiniteSieveWindow.primeWindow L R).card : ℝ) ≤
      (R-L)*SieveFullCutoffTransfer.fullUpper T z + remainder T z L R := by
  have hc : ((FiniteSieveWindow.primeWindow L R).card : ℝ) ≤
      ((SieveDivisorWindow.siftedWindow (SieveSmallWeights.pool z) L R).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (primeWindow_subset_sifted z L R hL hLR hzL)
  exact hc.trans (sifted_count_le T z L R hL hLR)

theorem prime_count_le_of_fullUpper (T z L R C : ℝ)
    (hL : 0 ≤ L) (hLR : L ≤ R) (hzL : z ≤ L)
    (hupper : SieveFullCutoffTransfer.fullUpper T z ≤
      C*SieveStoppingExpansion.primeEuler z) :
    ((FiniteSieveWindow.primeWindow L R).card : ℝ) ≤
      C*(R-L)*SieveStoppingExpansion.primeEuler z + remainder T z L R := by
  have hm := mul_le_mul_of_nonneg_left hupper (sub_nonneg.mpr hLR)
  have h := prime_count_le T z L R hL hLR hzL
  nlinarith

theorem prime_window_le_of_fullUpper (T z L y C : ℝ)
    (hL : 0 ≤ L) (hy : 0 ≤ y) (hzL : z ≤ L)
    (hupper : SieveFullCutoffTransfer.fullUpper T z ≤
      C*SieveStoppingExpansion.primeEuler z) :
    ((FiniteSieveWindow.primeWindow L (L+y)).card : ℝ) ≤
      C*y*SieveStoppingExpansion.primeEuler z + remainder T z L (L+y) := by
  simpa only [add_sub_cancel_left] using
    prime_count_le_of_fullUpper T z L (L+y) C hL (by linarith) hzL hupper

run_cmd do
  for decl in [``reciprocalMass_eq_fullUpper, ``remainder_eq_sum, ``sifted_count_le,
      ``primeWindow_subset_sifted, ``prime_count_le, ``prime_count_le_of_fullUpper,
      ``prime_window_le_of_fullUpper] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL UPPER PRIME WINDOW; SIGNED DIVISOR REMAINDER RETAINED"
end SieveUpperSelectedWindow
end
