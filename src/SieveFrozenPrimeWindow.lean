import SieveRosserWindow

/-! A fixed prime cutoff for many real windows. The cutoff and constructed
weights remain fixed while the endpoints vary, so this identity does not
introduce coefficients depending on a spatial integration variable. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace SieveFrozenPrimeWindow
open Erdos374.HarmanAnalytic151

def cutoff (N : ℕ) : ℕ := Nat.sqrt N + 1

theorem sifted_eq_primeWindow (N : ℕ) (hN : 1 ≤ N) (L R : ℝ)
    (hR : ⌊R⌋₊ ≤ N) (hleft : Nat.sqrt N ≤ ⌊L⌋₊) :
    SieveDivisorWindow.siftedWindow (primeBand 0 (cutoff N)) L R =
      FiniteSieveWindow.primeWindow L R := by
  rw [SieveDivisorWindow.siftedWindow_primeBand]
  ext n
  simp only [sifted, FiniteSieveWindow.primeWindow, Finset.mem_filter]
  constructor
  · rintro ⟨hn, hr⟩
    have hb := Finset.mem_Ioc.mp hn
    exact ⟨hn, (FiniteSieveWindow.rough_iff_prime N n hN
      (hleft.trans_lt hb.1) (hb.2.trans hR)).mp hr⟩
  · rintro ⟨hn, hp⟩
    have hb := Finset.mem_Ioc.mp hn
    exact ⟨hn, (FiniteSieveWindow.rough_iff_prime N n hN
      (hleft.trans_lt hb.1) (hb.2.trans hR)).mpr hp⟩

/-- Real endpoint guards imply the exact natural-floor guards. -/
theorem sifted_eq_primeWindow_of_real_bounds (N : ℕ) (hN : 1 ≤ N) (L R : ℝ)
    (hL : 0 ≤ L) (hR : R ≤ (N : ℝ)) (hleft : (Nat.sqrt N : ℝ) ≤ L) :
    SieveDivisorWindow.siftedWindow (primeBand 0 (cutoff N)) L R =
      FiniteSieveWindow.primeWindow L R := by
  apply sifted_eq_primeWindow N hN L R
  · simpa only [Nat.floor_natCast] using Nat.floor_mono hR
  · exact (Nat.le_floor_iff hL).mpr hleft

theorem selected_prime_count_bounds (N : ℕ) (hN : 1 ≤ N)
    (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (hnd : ps.Nodup) (hp : ∀ p ∈ ps, p.Prime)
    (hps : ps.toFinset = primeBand 0 (cutoff N))
    (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R)
    (hR : ⌊R⌋₊ ≤ N) (hleft : Nat.sqrt N ≤ ⌊L⌋₊) :
    (R-L) * HarmanDivisorWindow.reciprocalMass
        (SieveSelectedWindow.support gate false d ps) (SieveSelectedWindow.coefficient gate false d ps) +
      HarmanDivisorWindow.remainder
        (SieveSelectedWindow.support gate false d ps) (SieveSelectedWindow.coefficient gate false d ps) L R ≤
          ((FiniteSieveWindow.primeWindow L R).card : ℝ) ∧
      ((FiniteSieveWindow.primeWindow L R).card : ℝ) ≤
        (R-L) * HarmanDivisorWindow.reciprocalMass
          (SieveSelectedWindow.support gate true d ps) (SieveSelectedWindow.coefficient gate true d ps) +
        HarmanDivisorWindow.remainder
          (SieveSelectedWindow.support gate true d ps) (SieveSelectedWindow.coefficient gate true d ps) L R := by
  have h := SieveSelectedWindow.main_remainder_bounds gate d ps hnd hp L R hL hLR
  rw [hps, sifted_eq_primeWindow N hN L R hR hleft] at h
  exact h

theorem rosser_prime_count_bounds (N : ℕ) (hN : 1 ≤ N) (D : ℝ) (ps : List ℕ)
    (hnd : ps.Nodup) (hp : ∀ p ∈ ps, p.Prime)
    (hps : ps.toFinset = primeBand 0 (cutoff N))
    (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R)
    (hR : ⌊R⌋₊ ≤ N) (hleft : Nat.sqrt N ≤ ⌊L⌋₊) :
    (R-L) * HarmanDivisorWindow.reciprocalMass
        (SieveRosserWindow.support D false ps) (SieveRosser.coefficient D false ps) +
      HarmanDivisorWindow.remainder
        (SieveRosserWindow.support D false ps) (SieveRosser.coefficient D false ps) L R ≤
          ((FiniteSieveWindow.primeWindow L R).card : ℝ) ∧
      ((FiniteSieveWindow.primeWindow L R).card : ℝ) ≤
        (R-L) * HarmanDivisorWindow.reciprocalMass
          (SieveRosserWindow.support D true ps) (SieveRosser.coefficient D true ps) +
        HarmanDivisorWindow.remainder
          (SieveRosserWindow.support D true ps) (SieveRosser.coefficient D true ps) L R :=
  selected_prime_count_bounds N hN (SieveRosser.cubicGate D) 1 ps hnd hp hps
    L R hL hLR hR hleft

theorem rosser_backward_prime_count_bounds (N : ℕ) (hN : 1 ≤ N) (D : ℝ) (ps : List ℕ)
    (hnd : ps.Nodup) (hp : ∀ p ∈ ps, p.Prime)
    (hps : ps.toFinset = primeBand 0 (cutoff N))
    (x y : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hx : ⌊x⌋₊ ≤ N) (hleft : Nat.sqrt N ≤ ⌊x-y⌋₊) :
    y * HarmanDivisorWindow.reciprocalMass
        (SieveRosserWindow.support D false ps) (SieveRosser.coefficient D false ps) +
      HarmanDivisorWindow.remainder
        (SieveRosserWindow.support D false ps) (SieveRosser.coefficient D false ps) (x-y) x ≤
          ((FiniteSieveWindow.primeWindow (x-y) x).card : ℝ) ∧
      ((FiniteSieveWindow.primeWindow (x-y) x).card : ℝ) ≤
        y * HarmanDivisorWindow.reciprocalMass
          (SieveRosserWindow.support D true ps) (SieveRosser.coefficient D true ps) +
        HarmanDivisorWindow.remainder
          (SieveRosserWindow.support D true ps) (SieveRosser.coefficient D true ps) (x-y) x := by
  simpa only [sub_sub_cancel] using
    rosser_prime_count_bounds N hN D ps hnd hp hps (x-y) x (by linarith) (by linarith) hx hleft

end SieveFrozenPrimeWindow

run_cmd do
  for target in [``SieveFrozenPrimeWindow.sifted_eq_primeWindow,
      ``SieveFrozenPrimeWindow.sifted_eq_primeWindow_of_real_bounds,
      ``SieveFrozenPrimeWindow.selected_prime_count_bounds,
      ``SieveFrozenPrimeWindow.rosser_prime_count_bounds,
      ``SieveFrozenPrimeWindow.rosser_backward_prime_count_bounds] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "FIXED CUTOFF ACTUAL PRIME WINDOW BOUNDS PASSED; NO POSITIVITY CLAIM"

end
