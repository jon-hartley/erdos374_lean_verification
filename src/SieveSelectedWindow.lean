import SieveDivisorWindow
import SievePrimeSubsetEvaluation
import SievePrefix

/-! The actual recursive prefix selectors, collected into signed divisor
coefficients, give finite interval bounds. No pointwise sieve inequality is
an input: it is proved by the recursion. No quantitative reciprocal main
term or prime positivity is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace SieveSelectedWindow

/-- Actual integer support of the recursively selected subsets. -/
def support (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ) (ps : List ℕ) : Finset ℕ :=
  SievePrimeSubset.selectedSupport (SievePrefix.selected gate upper d ps)

def coefficient (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ) (ps : List ℕ) : ℕ → ℝ :=
  SievePrimeSubset.selectedCoefficient (SievePrefix.selected gate upper d ps)

theorem selected_primes (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ) (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) :
    ∀ s ∈ SievePrefix.selected gate upper d ps, ∀ p ∈ s, p.Prime := by
  intro s hs p hps
  exact hp p (List.mem_toFinset.mp (SievePrefix.selected_subset gate upper d ps s hs hps))

theorem support_positive (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ) (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) : ∀ m ∈ support gate upper d ps, 0 < m := by
  intro m hm
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hm
  exact Finset.prod_pos (fun p hps => (selected_primes gate upper d ps hp s hs p hps).pos)

theorem coefficient_abs_le_one (gate : ℕ → ℕ → Prop) (upper : Bool)
    (d : ℕ) (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime) (m : ℕ) :
    |coefficient gate upper d ps m| ≤ 1 :=
  SievePrimeSubset.selectedCoefficient_abs_le_one _ (selected_primes gate upper d ps hp) m

theorem evaluation_eq_value (gate : ℕ → ℕ → Prop) (upper : Bool)
    (d : ℕ) (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime) (n : ℕ) :
    SieveDivisorWindow.evaluation (support gate upper d ps) (coefficient gate upper d ps) n =
      SievePrefix.value gate upper d ps (fun p => if p ∣ n then (1 : ℝ) else 0) := by
  classical
  simpa only [support, coefficient, SieveDivisorWindow.evaluation,
    SievePrefix.value, SievePrefix.term] using
    SievePrimeSubset.selectedCoefficient_dvd_eq_product
      (SievePrefix.selected gate upper d ps) (selected_primes gate upper d ps hp) n

/-- Pointwise lower and upper bounds for these actual coefficients. -/
theorem evaluation_bounds (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (hnd : ps.Nodup) (hp : ∀ p ∈ ps, p.Prime) (n : ℕ) :
    SieveDivisorWindow.evaluation (support gate false d ps) (coefficient gate false d ps) n ≤
        SieveDivisorWindow.indicator ps.toFinset n ∧
      SieveDivisorWindow.indicator ps.toFinset n ≤
        SieveDivisorWindow.evaluation (support gate true d ps) (coefficient gate true d ps) n := by
  classical
  rw [evaluation_eq_value gate false d ps hp n, evaluation_eq_value gate true d ps hp n,
    SieveDivisorWindow.indicator_eq_product]
  exact SievePrefix.value_bounds gate d ps (fun p => if p ∣ n then (1 : ℝ) else 0) hnd
    (by intro p _; split_ifs <;> norm_num)

theorem count_bounds (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (hnd : ps.Nodup) (hp : ∀ p ∈ ps, p.Prime) (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) :
    HarmanDivisorWindow.divisorCount (support gate false d ps) (coefficient gate false d ps) L R ≤
        ((SieveDivisorWindow.siftedWindow ps.toFinset L R).card : ℝ) ∧
      ((SieveDivisorWindow.siftedWindow ps.toFinset L R).card : ℝ) ≤
        HarmanDivisorWindow.divisorCount (support gate true d ps) (coefficient gate true d ps) L R :=
  SieveDivisorWindow.count_bounds_of_pointwise ps.toFinset
    (support gate false d ps) (support gate true d ps)
    (coefficient gate false d ps) (coefficient gate true d ps) L R
    (support_positive gate false d ps hp) (support_positive gate true d ps hp) hL hLR
    (fun n _ => evaluation_bounds gate d ps hnd hp n)

theorem main_remainder_bounds (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (hnd : ps.Nodup) (hp : ∀ p ∈ ps, p.Prime) (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) :
    (R-L) * HarmanDivisorWindow.reciprocalMass (support gate false d ps) (coefficient gate false d ps) +
        HarmanDivisorWindow.remainder (support gate false d ps) (coefficient gate false d ps) L R ≤
          ((SieveDivisorWindow.siftedWindow ps.toFinset L R).card : ℝ) ∧
      ((SieveDivisorWindow.siftedWindow ps.toFinset L R).card : ℝ) ≤
        (R-L) * HarmanDivisorWindow.reciprocalMass (support gate true d ps) (coefficient gate true d ps) +
          HarmanDivisorWindow.remainder (support gate true d ps) (coefficient gate true d ps) L R := by
  simpa only [SieveDivisorWindow.divisorCount_eq_main_add_remainder] using
    count_bounds gate d ps hnd hp L R hL hLR

theorem prime_count_bounds (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (hnd : ps.Nodup) (hp : ∀ p ∈ ps, p.Prime) (L R : ℝ)
    (hL : 1 ≤ L) (hLR : L ≤ R) (hsqrt : Nat.sqrt ⌊R⌋₊ ≤ ⌊L⌋₊)
    (hps : ps.toFinset = Erdos374.HarmanAnalytic151.primeBand 0 (FiniteSieveWindow.topCutoff R)) :
    (R-L) * HarmanDivisorWindow.reciprocalMass (support gate false d ps) (coefficient gate false d ps) +
        HarmanDivisorWindow.remainder (support gate false d ps) (coefficient gate false d ps) L R ≤
          ((FiniteSieveWindow.primeWindow L R).card : ℝ) ∧
      ((FiniteSieveWindow.primeWindow L R).card : ℝ) ≤
        (R-L) * HarmanDivisorWindow.reciprocalMass (support gate true d ps) (coefficient gate true d ps) +
          HarmanDivisorWindow.remainder (support gate true d ps) (coefficient gate true d ps) L R := by
  have h := main_remainder_bounds gate d ps hnd hp L R (by linarith) hLR
  rw [hps, SieveDivisorWindow.siftedWindow_top_eq_primeWindow L R hL hLR hsqrt] at h
  exact h

end SieveSelectedWindow

run_cmd do
  for target in [``SieveSelectedWindow.selected_primes, ``SieveSelectedWindow.support_positive,
      ``SieveSelectedWindow.coefficient_abs_le_one, ``SieveSelectedWindow.evaluation_eq_value,
      ``SieveSelectedWindow.evaluation_bounds, ``SieveSelectedWindow.count_bounds,
      ``SieveSelectedWindow.main_remainder_bounds, ``SieveSelectedWindow.prime_count_bounds] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "ACTUAL SELECTED SIEVE WINDOW BOUNDS PASSED; NO MAIN TERM POSITIVITY CLAIM"

end
