import SieveUpperBoxMass
import SieveNormalizedStoppingLoss

/-! The positive stopping excess in the actual upper boxed main term is
uniformly small on the Euler-product scale. Boundary and collision terms
remain separate; no arithmetic remainder is bounded here. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real Filter
open scoped BigOperators Topology
namespace SieveUpperNormalizedStoppingLoss
open SieveStoppingExpansion SieveBoxMass SieveUpperModelLoss
open SieveNormalizedStoppingLoss (normalizedError)

/-- The same explicit budget `2*C*exp(2)*s⁻¹⁰*exp(-1/s)` controls the
actual upper stopping excess. The D threshold precedes the upper cutoff. -/
theorem eventually_excess_bound (s : ℝ) (hs : 0 < s) (hsHalf : s ≤ 1/2) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
      D^(s^2) ≤ z → z ≤ D →
        excess D s z ≤ normalizedError s*primeEuler z := by
  obtain ⟨D₁, hD₁, hbox⟩ := SieveBoxMassTwo.small_parameter_bounds_two s hs hsHalf
  have ht : Tendsto (fun D : ℝ => log (D^(s^2))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_rpow_atTop (sq_pos_of_pos hs))
  obtain ⟨D₂, hD₂⟩ := eventually_atTop.mp
    (ht.eventually_ge_atTop PrimeEulerDimensionOne.errorConstant)
  refine ⟨max D₁ D₂, hD₁.trans_le (le_max_left _ _), ?_⟩
  intro D hD z hu hz
  have hD1 : 1 < D := hD₁.trans_le ((le_max_left _ _).trans hD)
  obtain ⟨h17, hband, _, hprime, _⟩ := hbox D ((le_max_left _ _).trans hD) z hz
  have hK := hD₂ D ((le_max_right _ _).trans hD)
  have heuler := SieveNormalizedStoppingLoss.euler_le_scaled D s z hD1 hs hu hz
    (by linarith) hK
  have hC : 0 ≤ SieveSmallPrimeFundamental.decayConstant :=
    SieveSmallPrimeFundamental.decayConstant_pos.le
  have hδ : 0 ≤ SieveSmallPrimeFundamental.decayConstant*exp (-1/s) := by positivity
  have hm := SieveUpperBoxMass.total_mass_le_exp_of_band_bound D s z hD1 hs hz
    (fun i _ => (hband i).trans (by norm_num))
  have hdef := (excess_le_decay D s z hD1 hs hsHalf).trans
    (mul_le_mul_of_nonneg_left hm (mul_nonneg hδ (SieveModelLoss.euler_pos D s).le))
  have hprofile : exp (2*primeMass D s z) ≤ exp 2*(1/s)^8 := by
    apply (exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hprime (by norm_num : (0:ℝ) ≤ 2))).trans_eq
    exact SieveStoppingBudget.profile_exp_identity s hs
  have hV : 0 ≤ primeEuler z := (SieveEulerRatio.euler_pos z).le
  calc
    _ ≤ (SieveSmallPrimeFundamental.decayConstant*exp (-1/s))*
        SieveModelLoss.euler D s*exp (2*primeMass D s z) := hdef
    _ ≤ ((SieveSmallPrimeFundamental.decayConstant*exp (-1/s))*
        ((2/s^2)*primeEuler z))*(exp 2*(1/s)^8) :=
      mul_le_mul (mul_le_mul_of_nonneg_left heuler hδ) hprofile
        (exp_pos _).le (by positivity)
    _ = normalizedError s*primeEuler z := by
      unfold normalizedError SieveStoppingBudget.error
      simp only [one_div]
      ring

/-- Every analytic stopping input is discharged. The quantifier order is
small fixed s, then one D threshold valid for every admissible z. -/
theorem uniformly_small_stopping_excess (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D → excess D s z ≤ ε*primeEuler z := by
  obtain ⟨s₁, hs₁, herror⟩ :=
    SieveStoppingBudget.error_small SieveSmallPrimeFundamental.decayConstant ε hε
  refine ⟨min s₁ (1/2), lt_min hs₁ (by norm_num), min_le_right _ _, ?_⟩
  intro s hs hss
  have hsHalf : s ≤ 1/2 := (hss.trans_le (min_le_right _ _)).le
  obtain ⟨D₀, hD₀, hb⟩ := eventually_excess_bound s hs hsHalf
  refine ⟨D₀, hD₀, fun D hD z hu hz => ?_⟩
  exact (hb D hD z hu hz).trans
    (mul_le_mul_of_nonneg_right (herror s hs (hss.trans_le (min_le_left _ _))).le
      (SieveEulerRatio.euler_pos z).le)

run_cmd do
  for decl in [``eventually_excess_bound, ``uniformly_small_stopping_excess] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL UPPER STOPPING EXCESS IS UNIFORMLY SMALL RELATIVE TO V(z)"
end SieveUpperNormalizedStoppingLoss
end
