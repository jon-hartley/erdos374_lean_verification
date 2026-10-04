import FlatDirichletScale
import PolynomialLogEnvelope

/-!
Absorb the fixed factor in flat polynomial cancellation and allow any
prescribed positive ceiling on the saving exponent.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Filter

namespace FlatPowerCap

theorem eventually_bound (ε ρ ceiling : ℝ) (hε : 0 < ε)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1) (hceiling : 0 < ceiling) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ ceiling ∧ ∀ᶠ X : ℝ in atTop,
      1 ≤ X ∧ ∀ N lo hi : ℕ, X ^ ε ≤ (N : ℝ) → (N : ℝ) ≤ X →
        N ≤ lo → hi ≤ 2 * N → ∀ t σ : ℝ,
          X ^ ρ ≤ |t| → |t| ≤ X → 1 ≤ σ →
          ‖Erdos374.HarmanGram152.verticalDirichlet152
            (Finset.Ioc lo hi) (fun _ => 1) σ t‖ ≤ X ^ (-κ) := by
  obtain ⟨δ, hδ, X₀, hX₀, hflat⟩ :=
    FlatDirichletScale.ambient_power_saving ε ρ hε hρ hρone
  let κ := min (δ / 2) ceiling
  have hκ : 0 < κ := lt_min (by positivity) hceiling
  refine ⟨κ, hκ, min_le_right _ _, ?_⟩
  filter_upwards [eventually_ge_atTop X₀,
    PolynomialLogEnvelope.eventually_constant_bound 10 (δ / 2) (by norm_num) (by positivity)]
    with X hX hconstant
  refine ⟨hconstant.1, ?_⟩
  intro N lo hi hNlower hNupper hlo hhi t σ htlow hthigh hσ
  have hXp : 0 < X := by linarith [hconstant.1]
  calc
    _ ≤ 10 * X ^ (-δ) := hflat X hX N lo hi hNlower hNupper hlo hhi t σ htlow hthigh hσ
    _ ≤ X ^ (δ / 2) * X ^ (-δ) :=
      mul_le_mul_of_nonneg_right hconstant.2 (Real.rpow_nonneg hXp.le _)
    _ = X ^ (-(δ / 2)) := by rw [← Real.rpow_add hXp]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hconstant.1
      (neg_le_neg (min_le_left (δ / 2) ceiling))

end FlatPowerCap

#print axioms FlatPowerCap.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``FlatPowerCap.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FLAT POWER CAP PASSED"
