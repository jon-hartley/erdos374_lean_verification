import SieveSelectedWindow
import SieveRosser

/-! Interval inequalities for the actual finite cubic-gate Rosser selectors.
The coefficients below are constructed, not existentially postulated. The
reciprocal sums are left literal; their quantitative lower bounds and the
source's boxed remainder decomposition are separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace SieveRosserWindow

def support (D : ℝ) (upper : Bool) (ps : List ℕ) : Finset ℕ :=
  SievePrimeSubset.selectedSupport (SieveRosser.selected D upper ps)

theorem support_positive (D : ℝ) (upper : Bool) (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) : ∀ m ∈ support D upper ps, 0 < m :=
  SieveSelectedWindow.support_positive (SieveRosser.cubicGate D) upper 1 ps hp

theorem evaluation_bounds (D : ℝ) (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, p.Prime) (n : ℕ) :
    SieveDivisorWindow.evaluation (support D false ps) (SieveRosser.coefficient D false ps) n ≤
        SieveDivisorWindow.indicator ps.toFinset n ∧
      SieveDivisorWindow.indicator ps.toFinset n ≤
        SieveDivisorWindow.evaluation (support D true ps) (SieveRosser.coefficient D true ps) n :=
  SieveSelectedWindow.evaluation_bounds (SieveRosser.cubicGate D) 1 ps hnd hp n

theorem count_bounds (D : ℝ) (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, p.Prime) (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) :
    HarmanDivisorWindow.divisorCount (support D false ps) (SieveRosser.coefficient D false ps) L R ≤
        ((SieveDivisorWindow.siftedWindow ps.toFinset L R).card : ℝ) ∧
      ((SieveDivisorWindow.siftedWindow ps.toFinset L R).card : ℝ) ≤
        HarmanDivisorWindow.divisorCount (support D true ps) (SieveRosser.coefficient D true ps) L R :=
  SieveSelectedWindow.count_bounds (SieveRosser.cubicGate D) 1 ps hnd hp L R hL hLR

theorem main_remainder_bounds (D : ℝ) (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, p.Prime) (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) :
    (R-L) * HarmanDivisorWindow.reciprocalMass (support D false ps) (SieveRosser.coefficient D false ps) +
        HarmanDivisorWindow.remainder (support D false ps) (SieveRosser.coefficient D false ps) L R ≤
          ((SieveDivisorWindow.siftedWindow ps.toFinset L R).card : ℝ) ∧
      ((SieveDivisorWindow.siftedWindow ps.toFinset L R).card : ℝ) ≤
        (R-L) * HarmanDivisorWindow.reciprocalMass (support D true ps) (SieveRosser.coefficient D true ps) +
          HarmanDivisorWindow.remainder (support D true ps) (SieveRosser.coefficient D true ps) L R :=
  SieveSelectedWindow.main_remainder_bounds (SieveRosser.cubicGate D) 1 ps hnd hp L R hL hLR

/-- Fully expanded reciprocal main terms and literal open-left floor errors. -/
theorem literal_bounds (D : ℝ) (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, p.Prime) (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) :
    (R-L) * (∑ m ∈ support D false ps, SieveRosser.coefficient D false ps m / m) +
        (∑ m ∈ support D false ps, SieveRosser.coefficient D false ps m *
          ((⌊R / m⌋₊ : ℝ) - (⌊L / m⌋₊ : ℝ) - (R-L) / m)) ≤
          ((SieveDivisorWindow.siftedWindow ps.toFinset L R).card : ℝ) ∧
      ((SieveDivisorWindow.siftedWindow ps.toFinset L R).card : ℝ) ≤
        (R-L) * (∑ m ∈ support D true ps, SieveRosser.coefficient D true ps m / m) +
          (∑ m ∈ support D true ps, SieveRosser.coefficient D true ps m *
            ((⌊R / m⌋₊ : ℝ) - (⌊L / m⌋₊ : ℝ) - (R-L) / m)) := by
  simpa only [HarmanDivisorWindow.reciprocalMass, HarmanDivisorWindow.remainder_eq_sum] using
    main_remainder_bounds D ps hnd hp L R hL hLR

theorem backward_main_remainder_bounds (D : ℝ) (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, p.Prime) (x y : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x) :
    y * HarmanDivisorWindow.reciprocalMass (support D false ps) (SieveRosser.coefficient D false ps) +
        HarmanDivisorWindow.remainder (support D false ps) (SieveRosser.coefficient D false ps) (x-y) x ≤
          ((SieveDivisorWindow.siftedWindow ps.toFinset (x-y) x).card : ℝ) ∧
      ((SieveDivisorWindow.siftedWindow ps.toFinset (x-y) x).card : ℝ) ≤
        y * HarmanDivisorWindow.reciprocalMass (support D true ps) (SieveRosser.coefficient D true ps) +
          HarmanDivisorWindow.remainder (support D true ps) (SieveRosser.coefficient D true ps) (x-y) x := by
  simpa only [sub_sub_cancel] using
    main_remainder_bounds D ps hnd hp (x-y) x (by linarith) (by linarith)

theorem prime_count_bounds (D : ℝ) (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, p.Prime) (L R : ℝ)
    (hL : 1 ≤ L) (hLR : L ≤ R) (hsqrt : Nat.sqrt ⌊R⌋₊ ≤ ⌊L⌋₊)
    (hps : ps.toFinset = Erdos374.HarmanAnalytic151.primeBand 0 (FiniteSieveWindow.topCutoff R)) :
    (R-L) * HarmanDivisorWindow.reciprocalMass (support D false ps) (SieveRosser.coefficient D false ps) +
        HarmanDivisorWindow.remainder (support D false ps) (SieveRosser.coefficient D false ps) L R ≤
          ((FiniteSieveWindow.primeWindow L R).card : ℝ) ∧
      ((FiniteSieveWindow.primeWindow L R).card : ℝ) ≤
        (R-L) * HarmanDivisorWindow.reciprocalMass (support D true ps) (SieveRosser.coefficient D true ps) +
          HarmanDivisorWindow.remainder (support D true ps) (SieveRosser.coefficient D true ps) L R :=
  SieveSelectedWindow.prime_count_bounds (SieveRosser.cubicGate D) 1 ps hnd hp L R hL hLR hsqrt hps

end SieveRosserWindow

run_cmd do
  for target in [``SieveRosserWindow.support_positive, ``SieveRosserWindow.evaluation_bounds,
      ``SieveRosserWindow.count_bounds, ``SieveRosserWindow.main_remainder_bounds,
      ``SieveRosserWindow.literal_bounds, ``SieveRosserWindow.backward_main_remainder_bounds,
      ``SieveRosserWindow.prime_count_bounds] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "ACTUAL ROSSER FINITE WINDOW BOUNDS PASSED; RECIPROCAL ASYMPTOTIC NOT ASSERTED"

end
