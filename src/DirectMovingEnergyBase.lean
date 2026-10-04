import PairSpacingCollectedEnergy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Exact h-independent collected coefficients. Signed collisions are
collected before any bound; no coefficient cap is transferred through
division by a possibly vanishing modulation. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos374.DirectMovingEnergy
open PairSpacingRational PairSpacingMeanSquare PairSpacingKernel PairSpacingCollectedEnergy

def baseRepresentation (a : ℕ → ℝ) (p : ℕ × ℤ) : ℂ :=
  (a p.1 : ℂ) / (2 * Real.pi * Complex.I * p.2)

def baseCoefficient (Q F : ℕ) (a : ℕ → ℝ) (ξ : ℝ) : ℂ :=
  collectedCoefficient (representatives Q F) (baseRepresentation a) frequency ξ

def modulation (ξ h : ℝ) : ℂ :=
  1 - exponentialKernel (-(2*Real.pi*ξ)) h

theorem modulation_exp (ξ h : ℝ) :
    modulation ξ h = 1 - Complex.exp (-2 * Real.pi * Complex.I * ξ * h) := by
  unfold modulation exponentialKernel
  congr 2
  push_cast
  ring

theorem representation_eq_modulation (Q F : ℕ) (a : ℕ → ℝ) (h : ℝ)
    (p : ℕ × ℤ) (hp : p ∈ representatives Q F) :
    representationCoefficient a h p = modulation (frequency p) h * baseRepresentation a p := by
  obtain ⟨hn,hQ,hk,hF⟩ := mem_representatives hp
  have hn0 : 0 < p.1 := by omega
  rw [representationCoefficient, divisorCoefficient, dite_eq_left hn0,
    PairFourier.coefficient_exp hn0 h hk, modulation_exp]
  have he : (-2 * Real.pi * Complex.I * (frequency p : ℝ) * h : ℂ) =
      -2 * Real.pi * Complex.I * p.2 * h / p.1 := by
    simp only [frequency, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_natCast]
    ring
  rw [he]
  unfold baseRepresentation
  ring

theorem coefficient_eq_modulation (Q F : ℕ) (a : ℕ → ℝ) (h ξ : ℝ) :
    coefficient Q F a h ξ = modulation ξ h * baseCoefficient Q F a ξ := by
  classical
  unfold coefficient baseCoefficient collectedCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [representation_eq_modulation Q F a h p (Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2]

theorem modulation_continuous (ξ : ℝ) : Continuous (modulation ξ) :=
  continuous_const.sub (continuous_kernel _)

def lowFrequencies (Q F : ℕ) (H : ℝ) : Finset ℝ :=
  (frequencies Q F).filter (fun ξ => |ξ| ≤ 1/(4*H))

def highFrequencies (Q F : ℕ) (H : ℝ) : Finset ℝ :=
  (frequencies Q F).filter (fun ξ => ¬ |ξ| ≤ 1/(4*H))

theorem modulation_energy_le (Q F : ℕ) (a : ℕ → ℝ) (B h : ℝ)
    (hB : 0 ≤ B) (hh : 0 ≤ h)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (∑ ξ ∈ frequencies Q F, ‖modulation ξ h * baseCoefficient Q F a ξ‖ ^ 2) ≤
      B^2*h*SingletonHarmonic.harmonicSum Q^3 := by
  simpa only [coefficient_eq_modulation] using energy_le Q F a B h hB hh ha

run_cmd do
  for decl in [``modulation_exp, ``representation_eq_modulation,
      ``coefficient_eq_modulation, ``modulation_continuous, ``modulation_energy_le] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "EXACT SIGNED COLLECTED BASE COEFFICIENT AND MODULATION ENERGY"

end Erdos374.DirectMovingEnergy
