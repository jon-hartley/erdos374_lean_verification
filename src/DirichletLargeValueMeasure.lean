import NormalizedLargeValues
import SeparatedSetMeasure

/-!
Lebesgue outer-measure versions of the proved finite large-values counts.
The level set is the actual norm superlevel set on the stated interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace DirichletLargeValueMeasure
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare

def levelSet (F : ℝ → ℂ) (a T V : ℝ) : Set ℝ :=
  Icc a (a + T) ∩ {t | V ≤ ‖F t‖}

theorem measurable_levelSet (F : ℝ → ℂ) (a T V : ℝ) (hF : Continuous F) :
    MeasurableSet (levelSet F a T V) :=
  measurableSet_Icc.inter (isClosed_le continuous_const hF.norm).measurableSet

theorem level_measure_bound (F : ℝ → ℂ) (a T V C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ r : Finset ℝ,
      (∀ t ∈ r, a ≤ t ∧ t ≤ a + T) →
      (∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|) →
      (∀ t ∈ r, V ≤ ‖F t‖) → (r.card : ℝ) ≤ C) :
    volume (levelSet F a T V) ≤ ENNReal.ofReal (2 * C) := by
  apply SeparatedSetMeasure.volume_bound _ C hC
  intro r hr hsep
  exact hcount r (fun t ht => (hr ht).1) hsep (fun t ht => (hr ht).2)

theorem exponential_measure_bound (N lo hi : ℕ) (coeff : ℕ → ℂ)
    (a T E V : ℝ) (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N)
    (hT : 0 ≤ T) (hE : 0 < E) (hV : 0 < V)
    (henergy : (∑ n ∈ Finset.Ioc lo hi, ‖coeff n‖ ^ 2) ≤ E) :
    volume (levelSet (exponentialSum151 (Finset.Ioc lo hi) coeff (fun n => Real.log n))
      a T V) ≤ ENNReal.ofReal (516 * N * (1 + Real.log (T + 1)) *
        (E / V ^ 2 + 1024 ^ 2 * T * E ^ 3 *
          (1 + Real.log ((N : ℝ) + 1)) / V ^ 6)) := by
  have hGN : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by
      linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith
  have hGT : 0 ≤ 1 + Real.log (T + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
    linarith
  have hh := level_measure_bound
    (exponentialSum151 (Finset.Ioc lo hi) coeff (fun n => Real.log n)) a T V
    (258 * N * (1 + Real.log (T + 1)) *
      (E / V ^ 2 + 1024 ^ 2 * T * E ^ 3 *
        (1 + Real.log ((N : ℝ) + 1)) / V ^ 6)) (by positivity)
    (fun r hrange hsep hlarge => HuxleyLogLoss.count_bound N lo hi coeff r a T E V
      hN hlo hhi hT hE hV henergy hrange hsep hlarge)
  convert hh using 1
  congr 1
  ring

theorem normalized_measure_bound (N lo hi : ℕ) (coeff : ℕ → ℂ)
    (a T A V σ : ℝ) (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N)
    (hT : 0 ≤ T) (hA : 0 < A) (hV : 0 < V) (hσ : 1 ≤ σ)
    (henergy : (∑ n ∈ Finset.Ioc lo hi, ‖coeff n‖ ^ 2) ≤ A * N) :
    volume (levelSet (verticalDirichlet152 (Finset.Ioc lo hi) coeff σ) a T V) ≤
      ENNReal.ofReal (516 * (1 + Real.log (T + 1)) *
        (A / V ^ 2 + 1024 ^ 2 * T * A ^ 3 *
          (1 + Real.log ((N : ℝ) + 1)) / ((N : ℝ) ^ 2 * V ^ 6))) := by
  have hGN : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by
      linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith
  have hGT : 0 ≤ 1 + Real.log (T + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
    linarith
  have hh := level_measure_bound (verticalDirichlet152 (Finset.Ioc lo hi) coeff σ) a T V
    (258 * (1 + Real.log (T + 1)) *
      (A / V ^ 2 + 1024 ^ 2 * T * A ^ 3 *
        (1 + Real.log ((N : ℝ) + 1)) / ((N : ℝ) ^ 2 * V ^ 6))) (by positivity)
    (fun r hrange hsep hlarge => NormalizedLargeValues.count_bound N lo hi coeff r a T A V σ
      hN hlo hhi hT hA hV hσ henergy hrange hsep hlarge)
  convert hh using 1
  congr 1
  ring

end DirichletLargeValueMeasure

#print axioms DirichletLargeValueMeasure.normalized_measure_bound
run_cmd do
  for target in [``DirichletLargeValueMeasure.exponential_measure_bound,
      ``DirichletLargeValueMeasure.normalized_measure_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "DIRICHLET LARGE VALUE MEASURE PASSED"
