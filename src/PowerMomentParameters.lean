import NormalizedPowerLevel
import NormalizedEvenMoment

/-!
Exact coefficients for the whole hth power of a normalized Dirichlet
polynomial. The energy input allows the coefficient loss X^β.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PowerMomentParameters
open NormalizedPowerLevel DyadicLevelParameters
open Erdos374.HarmanGram152

def quadraticConstant (h : ℕ) : ℝ := 516 * (h : ℝ) ^ 3 * 2 ^ h
def sexticConstant (h : ℕ) : ℝ :=
  516 * 1024 ^ 2 * (h : ℝ) ^ 7 * 2 ^ h

def meanEven (C : ℝ) (N h : ℕ) (T α β X : ℝ) : ℝ :=
  C * (2 * (N : ℝ)) ^ α * (X ^ β) ^ h *
    (T / (N : ℝ) ^ h + 4 * (2 : ℝ) ^ h *
      (1 + h * Real.log (2 * (N : ℝ))))

theorem actual_even_bound (h : ℕ) (hh : 1 ≤ h)
    (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s : Finset ℕ) (N : ℕ) (coeff : ℕ → ℂ)
        (a T β X σ : ℝ),
        1 ≤ N → 0 ≤ T → 1 ≤ σ →
        (∀ n ∈ s, N ≤ n ∧ n ≤ 2 * N) →
        (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ X ^ β * N →
        (∫ t in Icc a (a + T),
          ‖verticalDirichlet152 s coeff σ t‖ ^ (2 * h)) ≤
          meanEven C N h T α β X := by
  obtain ⟨C, hC, hmoment⟩ :=
    NormalizedEvenMoment.integral_bound h hh α hα
  refine ⟨C, hC, ?_⟩
  intro s N coeff a T β X σ hN hT hσ hs he
  exact hmoment s N coeff a T (X ^ β) σ hN hT hσ hs he

theorem quadratic_eq (D : ℝ) (N h : ℕ) (T α β X : ℝ)
    (hN : 1 ≤ N) :
    quadratic (N ^ h) h T (energyBudget D N h α (X ^ β)) =
      quadraticConstant h * D * (2 * (N : ℝ)) ^ α *
        (X ^ β) ^ h * (1 + Real.log (T + 1)) := by
  have hNp : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  unfold quadratic energyBudget quadraticConstant
  push_cast
  rw [div_pow]
  field_simp

theorem sextic_eq (D : ℝ) (N h : ℕ) (T α β X : ℝ)
    (hN : 1 ≤ N) :
    sextic (N ^ h) h T (energyBudget D N h α (X ^ β)) =
      sexticConstant h * D ^ 3 * ((2 * (N : ℝ)) ^ α) ^ 3 *
        ((X ^ β) ^ h) ^ 3 * (1 + Real.log (T + 1)) *
        (1 + Real.log ((2 : ℝ) ^ h * (N : ℝ) ^ h + 1)) *
          T / (N : ℝ) ^ (2 * h) := by
  have hNp : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  unfold sextic energyBudget sexticConstant
  push_cast
  rw [div_pow]
  field_simp
  ring

theorem log_bounds (N h : ℕ) (T X : ℝ) (hN : 1 ≤ N)
    (hNX : (N : ℝ) ≤ X) (hT : 1 ≤ T) (hTX : T ≤ X) :
    1 ≤ 1 + Real.log X ∧
      Real.log (2 * (N : ℝ)) ≤ 1 + Real.log X ∧
      1 + Real.log (T + 1) ≤ 2 * (1 + Real.log X) ∧
      1 + Real.log ((2 : ℝ) ^ h * (N : ℝ) ^ h + 1) ≤
        ((h : ℝ) + 2) * (1 + Real.log X) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX : 1 ≤ X := hNR.trans hNX
  have hXp : 0 < X := by linarith
  have hNp : (0 : ℝ) < N := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hl2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlog2X : Real.log (2 * X) ≤ 1 + Real.log X := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXp.ne']
    linarith
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · exact (Real.log_le_log (by positivity : 0 < 2 * (N : ℝ))
      (by linarith)).trans hlog2X
  · have hh := (Real.log_le_log (by linarith : 0 < T + 1)
      (show T + 1 ≤ 2 * X by linarith)).trans hlog2X
    linarith
  · have hpow : (2 * (N : ℝ)) ^ h ≤ (2 * X) ^ h := by
      apply pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (N : ℝ))
      linarith
    have hone : 1 ≤ (2 * X) ^ h := one_le_pow₀ (by linarith)
    have hupper : (2 : ℝ) ^ h * (N : ℝ) ^ h + 1 ≤
        (2 * X) ^ (h + 1) := by
      rw [← mul_pow, pow_succ]
      calc
        (2 * (N : ℝ)) ^ h + 1 ≤ (2 * X) ^ h + 1 := by
          linarith
        _ ≤ 2 * (2 * X) ^ h := by linarith
        _ ≤ (2 * X) ^ h * (2 * X) := by
          nlinarith [mul_nonneg
            (show 0 ≤ (2 * X) ^ h by positivity)
            (show 0 ≤ X - 1 by linarith)]
    have hh := Real.log_le_log
      (by positivity : 0 < (2 : ℝ) ^ h * (N : ℝ) ^ h + 1)
      hupper
    rw [Real.log_pow] at hh
    have hmult := mul_le_mul_of_nonneg_left hlog2X
      (show (0 : ℝ) ≤ (h : ℝ) + 1 by positivity)
    push_cast at hh
    nlinarith [hlX]

end PowerMomentParameters

#print axioms PowerMomentParameters.log_bounds
run_cmd do
  for target in [``PowerMomentParameters.quadratic_eq,
      ``PowerMomentParameters.sextic_eq,
      ``PowerMomentParameters.log_bounds,
      ``PowerMomentParameters.actual_even_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "POWER MOMENT PARAMETERS PASSED"
