import DyadicPolynomialMeasure

/-!
Expose the quadratic and sixth-power coefficients of the dyadic level
bound, so the general continuous moment theorem applies directly.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace DyadicLevelParameters
open Erdos374.HarmanAnalytic151MeanSquare DirichletLargeValueMeasure

def quadratic (N k : ℕ) (T E : ℝ) : ℝ :=
  516 * (k : ℝ) ^ 3 * (2 ^ k * N : ℕ) * (1 + Real.log (T + 1)) * E

def sextic (N k : ℕ) (T E : ℝ) : ℝ :=
  516 * 1024 ^ 2 * (k : ℝ) ^ 7 * (2 ^ k * N : ℕ) *
    (1 + Real.log (T + 1)) * T * E ^ 3 * (1 + Real.log ((2 ^ k * N : ℕ) + 1))

theorem quadratic_nonnegative (N k : ℕ) (T E : ℝ) (hT : 0 ≤ T) (hE : 0 ≤ E) :
    0 ≤ quadratic N k T E := by
  have hlog := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
  unfold quadratic
  positivity

theorem sextic_positive (N k : ℕ) (T E : ℝ)
    (hN : 1 ≤ N) (hk : 1 ≤ k) (hT : 0 < T) (hE : 0 < E) :
    0 < sextic N k T E := by
  have hNp : (0 : ℝ) < (2 ^ k * N : ℕ) := by
    exact_mod_cast Nat.mul_pos (by positivity : 0 < (2 : ℕ) ^ k) (by omega : 0 < N)
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlogT := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
  have hlogN := Real.log_nonneg (show 1 ≤ ((2 ^ k * N : ℕ) : ℝ) + 1 by linarith)
  unfold sextic
  positivity

theorem measure_bound (N k : ℕ) (coeff : ℕ → ℂ) (a T E V : ℝ)
    (hN : 1 ≤ N) (hk : 1 ≤ k) (hT : 0 ≤ T) (hE : 0 < E) (hV : 0 < V)
    (henergy : (∑ n ∈ Finset.Ioc N (2 ^ k * N), ‖coeff n‖ ^ 2) ≤ E) :
    volume (levelSet (exponentialSum151 (Finset.Ioc N (2 ^ k * N)) coeff
      (fun n => Real.log n)) a T V) ≤
      ENNReal.ofReal (quadratic N k T E / V ^ 2 + sextic N k T E / V ^ 6) := by
  have hh := DyadicPolynomialMeasure.measure_bound N k coeff a T E V hN hk hT hE hV henergy
  convert hh using 1
  congr 1
  unfold quadratic sextic
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp

end DyadicLevelParameters

#print axioms DyadicLevelParameters.measure_bound
run_cmd do
  for decl in [``DyadicLevelParameters.measure_bound, ``DyadicLevelParameters.sextic_positive] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "DYADIC LEVEL PARAMETERS PASSED"
