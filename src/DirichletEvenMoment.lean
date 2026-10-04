import DirichletPowerEnergy
import DirichletPowerExpansion

/-!
Continuous even moments from exact polynomial powers. The constant
depends only on the fixed moment order and the positive power loss.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace DirichletEvenMoment
open DirichletPowerCoefficients Erdos374.HarmanAnalytic151MeanSquare

theorem integral_bound (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (s : Finset ℕ) (L : ℕ) (coeff : ℕ → ℂ) (a T : ℝ),
      1 ≤ L → 0 ≤ T → (∀ n ∈ s, 0 < n ∧ n ≤ L) →
      (∫ t in Icc a (a + T), ‖exponentialSum151 s coeff (fun n => Real.log n) t‖ ^ (2 * k)) ≤
        D * ((L ^ k : ℕ) : ℝ) ^ ε *
          (T + 4 * (L ^ k : ℕ) * (1 + Real.log (L ^ k : ℕ))) *
            (∑ n ∈ s, ‖coeff n‖ ^ 2) ^ k := by
  obtain ⟨D, hD, henergy⟩ := DirichletPowerEnergy.energy_bound k hk ε hε
  refine ⟨D, hD, ?_⟩
  intro s L coeff a T hL hT hs
  have hlen : (1 : ℝ) ≤ (L ^ k : ℕ) := by
    exact_mod_cast one_le_pow₀ hL (n := k)
  have hlog : 0 ≤ Real.log (L ^ k : ℕ) := Real.log_nonneg hlen
  have hfactor : 0 ≤ T + 4 * (L ^ k : ℕ) * (1 + Real.log (L ^ k : ℕ)) := by positivity
  have hm := dirichlet_mean_square_le151 (Finset.Icc 1 (L ^ k))
    (coefficient s k coeff) (L ^ k) (fun n hn => Finset.mem_Icc.mp hn) a (a + T)
  simp only [add_sub_cancel_left] at hm
  have hh := hm.trans (mul_le_mul_of_nonneg_left (henergy s L coeff hs) hfactor)
  simp_rw [DirichletPowerExpansion.norm_power s k L coeff _ hs]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show a ≤ a + T by linarith)]
  exact hh.trans_eq (by ring)

end DirichletEvenMoment

#print axioms DirichletEvenMoment.integral_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``DirichletEvenMoment.integral_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "DIRICHLET EVEN MOMENT PASSED"
