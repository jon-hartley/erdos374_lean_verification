import SieveVector
import SieveSelectedWindow

/-! Actual divisor-indicator and finite-window consequences of the vector
inequality. The two prime pools need not be disjoint for this pointwise result.
Collecting pairs by their product with a unit coefficient bound is a separate step. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators

namespace SieveVector

def selectedEvaluation (gate : ℕ → ℕ → Prop) (upper : Bool)
    (d : ℕ) (ps : List ℕ) (n : ℕ) : ℝ :=
  SieveDivisorWindow.evaluation (SieveSelectedWindow.support gate upper d ps)
    (SieveSelectedWindow.coefficient gate upper d ps) n

def lowerEvaluation (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ)
    (ps0 ps1 : List ℕ) (n : ℕ) : ℝ :=
  lowerKernel (selectedEvaluation gate0 false d0 ps0 n)
    (selectedEvaluation gate0 true d0 ps0 n)
    (selectedEvaluation gate1 false d1 ps1 n)
    (selectedEvaluation gate1 true d1 ps1 n)

def upperEvaluation (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ)
    (ps0 ps1 : List ℕ) (n : ℕ) : ℝ :=
  selectedEvaluation gate0 true d0 ps0 n * selectedEvaluation gate1 true d1 ps1 n

theorem indicator_nonneg (P : Finset ℕ) (n : ℕ) :
    0 ≤ SieveDivisorWindow.indicator P n := by
  classical
  unfold SieveDivisorWindow.indicator
  split_ifs <;> norm_num

theorem indicator_union (P Q : Finset ℕ) (n : ℕ) :
    SieveDivisorWindow.indicator (P ∪ Q) n =
      SieveDivisorWindow.indicator P n * SieveDivisorWindow.indicator Q n := by
  classical
  have hU : SieveDivisorWindow.avoids (P ∪ Q) n ↔
      SieveDivisorWindow.avoids P n ∧ SieveDivisorWindow.avoids Q n := by
    constructor
    · intro h
      exact ⟨fun p hp => h p (Finset.mem_union_left _ hp),
        fun p hp => h p (Finset.mem_union_right _ hp)⟩
    · rintro ⟨hP, hQ⟩ p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hP p hp
      · exact hQ p hp
  by_cases hP : SieveDivisorWindow.avoids P n <;>
    by_cases hQ : SieveDivisorWindow.avoids Q n <;>
      simp [SieveDivisorWindow.indicator, hU, hP, hQ]

/-- The recursive selectors supply both brackets; no pointwise sieve inequality
is an assumption. These are literal divisor evaluations of their coefficients. -/
theorem evaluation_bounds (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ)
    (ps0 ps1 : List ℕ) (hnd0 : ps0.Nodup) (hnd1 : ps1.Nodup)
    (hp0 : ∀ p ∈ ps0, p.Prime) (hp1 : ∀ p ∈ ps1, p.Prime) (n : ℕ) :
    lowerEvaluation gate0 gate1 d0 d1 ps0 ps1 n ≤
        SieveDivisorWindow.indicator (ps0.toFinset ∪ ps1.toFinset) n ∧
      SieveDivisorWindow.indicator (ps0.toFinset ∪ ps1.toFinset) n ≤
        upperEvaluation gate0 gate1 d0 d1 ps0 ps1 n := by
  have h0 := SieveSelectedWindow.evaluation_bounds gate0 d0 ps0 hnd0 hp0 n
  have h1 := SieveSelectedWindow.evaluation_bounds gate1 d1 ps1 hnd1 hp1 n
  have hg0 := indicator_nonneg ps0.toFinset n
  have hg1 := indicator_nonneg ps1.toFinset n
  rw [indicator_union]
  exact ⟨lowerKernel_le_product _ _ _ _ _ _ h0.1 h0.2 h1.1 h1.2 hg0 hg1,
    product_le_upper _ _ _ _ h0.2 h1.2 hg0 hg1⟩

theorem window_bounds (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ)
    (ps0 ps1 : List ℕ) (hnd0 : ps0.Nodup) (hnd1 : ps1.Nodup)
    (hp0 : ∀ p ∈ ps0, p.Prime) (hp1 : ∀ p ∈ ps1, p.Prime) (L R : ℝ) :
    (∑ n ∈ FiniteSieveWindow.window L R, lowerEvaluation gate0 gate1 d0 d1 ps0 ps1 n) ≤
        ((SieveDivisorWindow.siftedWindow (ps0.toFinset ∪ ps1.toFinset) L R).card : ℝ) ∧
      ((SieveDivisorWindow.siftedWindow (ps0.toFinset ∪ ps1.toFinset) L R).card : ℝ) ≤
        ∑ n ∈ FiniteSieveWindow.window L R, upperEvaluation gate0 gate1 d0 d1 ps0 ps1 n := by
  rw [← SieveDivisorWindow.sum_indicator_eq_card]
  exact ⟨Finset.sum_le_sum (fun n _ => (evaluation_bounds gate0 gate1 d0 d1 ps0 ps1
      hnd0 hnd1 hp0 hp1 n).1),
    Finset.sum_le_sum (fun n _ => (evaluation_bounds gate0 gate1 d0 d1 ps0 ps1
      hnd0 hnd1 hp0 hp1 n).2)⟩

/-- Actual two-coordinate coefficient kernels have absolute value at most one.
This is before any collection of coordinate pairs with equal integer product. -/
theorem coefficient_kernel_abs_le_one (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ)
    (ps0 ps1 : List ℕ) (hp0 : ∀ p ∈ ps0, p.Prime) (hp1 : ∀ p ∈ ps1, p.Prime)
    (m n : ℕ) :
    |lowerKernel (SieveSelectedWindow.coefficient gate0 false d0 ps0 m)
      (SieveSelectedWindow.coefficient gate0 true d0 ps0 m)
      (SieveSelectedWindow.coefficient gate1 false d1 ps1 n)
      (SieveSelectedWindow.coefficient gate1 true d1 ps1 n)| ≤ 1 :=
  selectedCoefficient_kernel_abs_le_one _ _ _ _
    (SieveSelectedWindow.selected_primes gate0 false d0 ps0 hp0)
    (SieveSelectedWindow.selected_primes gate0 true d0 ps0 hp0)
    (SieveSelectedWindow.selected_primes gate1 false d1 ps1 hp1)
    (SieveSelectedWindow.selected_primes gate1 true d1 ps1 hp1) m n

#print axioms evaluation_bounds
#print axioms coefficient_kernel_abs_le_one
run_cmd do
  for decl in [``indicator_nonneg, ``indicator_union, ``evaluation_bounds,
      ``window_bounds, ``coefficient_kernel_abs_le_one] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
run_cmd Lean.logInfo "SIEVE_VECTOR_DIVISOR_PASSED; ACTUAL SELECTED COEFFICIENTS; NO MAIN TERM POSITIVITY"

end SieveVector
end
