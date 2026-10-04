import PositiveSharpRemainderAnalysisBoxed
import PositiveSharpBoxedCount
import FiniteDivisorFamily

/-! Exact collection of the complete signed remainder on its physical
divisor index. The upper cofactor p is part of that index; there is no
additional 1/p multiplying the remainder. Overlapping supports are added,
and the lower source remainder contributes the negative lower coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PositiveSharpRemainderAnalysisPhysical
open PositiveSharpBoxedCount SieveWeightedCutoffs SieveWeightedScalarBudget
open SieveCappedUpperMainTerms (cappedFourth)

def inflatedSupport (p : ℕ) (S : Finset ℕ) : Finset ℕ :=
  FactoredDivisorWeights.support {p} S

def inflatedCoefficient (p : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) : ℕ → ℝ :=
  FactoredDivisorWeights.coefficient {p} S (fun _ => 1) w

theorem inflated_kernel (p : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    (∑ m ∈ inflatedSupport p S, inflatedCoefficient p S w m * f m) =
      ∑ m ∈ S, w m * f (p*m) := by
  simpa only [inflatedSupport, inflatedCoefficient, Finset.sum_product,
    Finset.sum_singleton, DirichletProductCoefficients.productIndex, one_mul] using
    FactoredDivisorWeights.grouped_sum {p} S (FactoredDivisorWeights.support {p} S)
      (fun _ => 1) w f (HarmanDivisorWindow.productSupport_contains {p} S)

theorem inflated_remainder (p : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) (L R : ℝ) :
    HarmanDivisorWindow.remainder (inflatedSupport p S) (inflatedCoefficient p S w) L R =
      HarmanDivisorWindow.remainder S w (L/p) (R/p) := by
  rw [HarmanDivisorWindow.remainder_eq_sum, inflated_kernel,
    HarmanDivisorWindow.remainder_eq_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Nat.cast_mul, ← div_div, sub_div]

def upperSupport (X s : ℝ) (P : Finset ℕ) (w : ℝ → ℝ) : Finset ℕ :=
  FiniteDivisorFamily.support P (fun p => inflatedSupport p
    (SieveUpperBoxWindow.support (level X s/p) s (w p)))

def upperCoefficient (X s : ℝ) (P : Finset ℕ) (w : ℝ → ℝ) : ℕ → ℝ :=
  FiniteDivisorFamily.coefficient P (fun p => inflatedSupport p
    (SieveUpperBoxWindow.support (level X s/p) s (w p))) (fun p =>
    inflatedCoefficient p (SieveUpperBoxWindow.support (level X s/p) s (w p))
      (SieveUpperBoxWindow.coefficient (level X s/p) s (w p)))

theorem upper_remainder (X s L R : ℝ) (P : Finset ℕ) (w : ℝ → ℝ) :
    HarmanDivisorWindow.remainder (upperSupport X s P w)
      (upperCoefficient X s P w) L R = upperRemainders X s L R P w := by
  rw [upperSupport, upperCoefficient, FiniteDivisorFamily.remainder_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact inflated_remainder p _ _ L R

def componentSupports (X s : ℝ) : Fin 3 → Finset ℕ :=
  ![SieveBoxedWindow.support (level X s) s (X^alpha s),
    upperSupport X s (largePrimes X) (cutoffThree X s),
    upperSupport X s (smallPrimes X s) (cappedFourth X s)]

def componentCoefficients (X s : ℝ) : Fin 3 → ℕ → ℝ :=
  ![fun m => -SieveBoxedWindow.coefficient (level X s) s (X^alpha s) m,
    upperCoefficient X s (largePrimes X) (cutoffThree X s),
    upperCoefficient X s (smallPrimes X s) (cappedFourth X s)]

def support (X s : ℝ) : Finset ℕ := FiniteDivisorFamily.support Finset.univ (componentSupports X s)

def coefficient (X s : ℝ) : ℕ → ℝ :=
  FiniteDivisorFamily.coefficient Finset.univ (componentSupports X s) (componentCoefficients X s)

theorem neg_remainder (S : Finset ℕ) (w : ℕ → ℝ) (L R : ℝ) :
    HarmanDivisorWindow.remainder S (fun m => -w m) L R =
      -HarmanDivisorWindow.remainder S w L R := by
  simp only [HarmanDivisorWindow.remainder_eq_sum, neg_mul, Finset.sum_neg_distrib]

/-- The entire actual signed remainder, with no restriction on tuple length
beyond the original actual families and no analytic estimate as a premise. -/
theorem signedRemainder_eq (X s x y : ℝ) :
    signedRemainder X s x y =
      HarmanDivisorWindow.remainder (support X s) (coefficient X s) (x-y) x := by
  rw [support, coefficient, FiniteDivisorFamily.remainder_eq_sum]
  simp only [componentSupports, componentCoefficients, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  rw [neg_remainder, upper_remainder, upper_remainder]
  unfold signedRemainder SieveBoxedWindow.sourceRemainder
  ring

run_cmd do
  for decl in [``inflated_kernel, ``inflated_remainder, ``upper_remainder,
      ``neg_remainder, ``signedRemainder_eq] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "COMPLETE SIGNED REMAINDER PHYSICAL COLLECTION PASSED"

end PositiveSharpRemainderAnalysisPhysical
