import SieveSmallPrimeFundamental
import SieveStoppingBudget
import SieveBoxMassTwo
import PrimeEulerDimensionOne

/-! The genuine stopping deficit in the boxed main term is arbitrarily small
relative to V(z), uniformly in the upper cutoff. Cubic-boundary discrepancies
and same-band collisions are separate contributions. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators Topology
open Real Set Filter

namespace SieveNormalizedStoppingLoss
open SieveStoppingExpansion SieveBoxMass

def normalizedError (s : ℝ) : ℝ :=
  SieveStoppingBudget.error SieveSmallPrimeFundamental.decayConstant s

theorem normalizedError_nonneg (s : ℝ) (hs : 0 < s) : 0 ≤ normalizedError s :=
  SieveStoppingBudget.error_nonneg _ s SieveSmallPrimeFundamental.decayConstant_pos.le hs

theorem tendsto_normalizedError_zero :
    Tendsto normalizedError (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  SieveStoppingBudget.tendsto_error_zero _

/-- Dimension-one normalization once the one absolute Euler error is absorbed
by log u. The threshold condition will be proved before choosing z. -/
theorem euler_ratio_le (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hu : D^(s^2) ≤ z) (hz : z ≤ D) (h2 : 2 ≤ D^(s^2))
    (hK : PrimeEulerDimensionOne.errorConstant ≤ log (D^(s^2))) :
    SieveModelLoss.euler D s / primeEuler z ≤ 2/s^2 := by
  have hD0 : 0 < D := by linarith
  have hlD : log D ≠ 0 := (log_pos hD).ne'
  have hlu : 0 < log (D^(s^2)) := log_pos (Real.one_lt_rpow hD (sq_pos_of_pos hs))
  have hz0 : 0 < z := (rpow_pos_of_pos hD0 _).trans_le hu
  have hK0 : 0 ≤ PrimeEulerDimensionOne.errorConstant :=
    PrimeEulerDimensionOne.errorConstant_pos.le
  have hratio : log z / log (D^(s^2)) ≤ 1/s^2 := by
    calc
      _ ≤ log D / log (D^(s^2)) :=
        div_le_div_of_nonneg_right (log_le_log hz0 hz) hlu.le
      _ = _ := by rw [Real.log_rpow hD0]; field_simp
  have hfac : 1+PrimeEulerDimensionOne.errorConstant/log (D^(s^2)) ≤ 2 := by
    have hh := (div_le_one hlu).mpr hK
    linarith
  change primeEuler (D^(s^2)) / primeEuler z ≤ _
  calc
    _ ≤ (log z/log (D^(s^2))) *
        (1+PrimeEulerDimensionOne.errorConstant/log (D^(s^2))) :=
      PrimeEulerDimensionOne.ratio_bound _ _ h2 hu
    _ ≤ (1/s^2)*2 := mul_le_mul hratio hfac (by positivity) (by positivity)
    _ = _ := by ring

theorem euler_le_scaled (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hu : D^(s^2) ≤ z) (hz : z ≤ D) (h2 : 2 ≤ D^(s^2))
    (hK : PrimeEulerDimensionOne.errorConstant ≤ log (D^(s^2))) :
    SieveModelLoss.euler D s ≤ (2/s^2)*primeEuler z :=
  (div_le_iff₀ (SieveEulerRatio.euler_pos z)).mp (euler_ratio_le D s z hD hs hu hz h2 hK)

/-- One D-threshold is selected before the actual upper prime cutoff. Both
the stopping losses and the prime/Euler inputs are discharged theorems. -/
theorem eventually_deficit_bound (s : ℝ) (hs : 0 < s) (hsHalf : s ≤ 1/2) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
      D^(s^2) ≤ z → z ≤ D →
        SieveModelLoss.deficit D s z ≤ normalizedError s * primeEuler z := by
  obtain ⟨D₁, hD₁, hbox⟩ := SieveBoxMassTwo.small_parameter_bounds_two s hs hsHalf
  have ht : Tendsto (fun D : ℝ => log (D^(s^2))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_rpow_atTop (sq_pos_of_pos hs))
  obtain ⟨D₂, hD₂⟩ := eventually_atTop.1
    (ht.eventually_ge_atTop PrimeEulerDimensionOne.errorConstant)
  refine ⟨max D₁ D₂, hD₁.trans_le (le_max_left _ _), ?_⟩
  intro D hD z hu hz
  have hD1 : 1 < D := hD₁.trans_le ((le_max_left _ _).trans hD)
  obtain ⟨h17, hband, _, hprime, _⟩ := hbox D ((le_max_left _ _).trans hD) z hz
  have hK := hD₂ D ((le_max_right _ _).trans hD)
  have heuler := euler_le_scaled D s z hD1 hs hu hz (by linarith) hK
  have hC : 0 ≤ SieveSmallPrimeFundamental.decayConstant :=
    SieveSmallPrimeFundamental.decayConstant_pos.le
  have hδ : 0 ≤ SieveSmallPrimeFundamental.decayConstant * exp (-1/s) := by positivity
  have hdef := SieveModelLoss.deficit_le_of_relative_loss D s z
    (SieveSmallPrimeFundamental.decayConstant * exp (-1/s)) hD1 hs hz
    (fun i _ => (hband i).trans (by norm_num))
    (fun mode => SieveSmallPrimeFundamental.relative_loss_bound D s mode hD1 hs hsHalf)
  have hprofile : exp (2*primeMass D s z) ≤ exp 2*(1/s)^8 := by
    apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hprime (by norm_num : (0:ℝ) ≤ 2))).trans_eq
    exact SieveStoppingBudget.profile_exp_identity s hs
  have hV : 0 ≤ primeEuler z := (SieveEulerRatio.euler_pos z).le
  calc
    _ ≤ (SieveSmallPrimeFundamental.decayConstant * exp (-1/s)) *
        SieveModelLoss.euler D s * exp (2*primeMass D s z) := hdef
    _ ≤ ((SieveSmallPrimeFundamental.decayConstant * exp (-1/s)) *
        ((2/s^2)*primeEuler z)) * (exp 2*(1/s)^8) :=
      mul_le_mul (mul_le_mul_of_nonneg_left heuler hδ) hprofile
        (exp_pos _).le (by positivity)
    _ = normalizedError s * primeEuler z := by
      unfold normalizedError SieveStoppingBudget.error
      simp only [one_div]
      ring

/-- The actual stopping part of the boxed-main-term deficit is uniformly
small on the Euler-product scale. No loss bound remains as a hypothesis. -/
theorem uniformly_small_stopping_deficit (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D →
          SieveModelLoss.deficit D s z ≤ ε * primeEuler z := by
  obtain ⟨s₁, hs₁, herror⟩ :=
    SieveStoppingBudget.error_small SieveSmallPrimeFundamental.decayConstant ε hε
  refine ⟨min s₁ (1/2), lt_min hs₁ (by norm_num), min_le_right _ _, ?_⟩
  intro s hs hss
  have hsHalf : s ≤ 1/2 := (hss.trans_le (min_le_right _ _)).le
  obtain ⟨D₀, hD₀, hbound⟩ := eventually_deficit_bound s hs hsHalf
  refine ⟨D₀, hD₀, fun D hD z hu hz => ?_⟩
  exact (hbound D hD z hu hz).trans
    (mul_le_mul_of_nonneg_right (herror s hs (hss.trans_le (min_le_left _ _))).le
      (SieveEulerRatio.euler_pos z).le)

run_cmd do
  for decl in [``normalizedError_nonneg, ``tendsto_normalizedError_zero,
    ``euler_ratio_le, ``euler_le_scaled, ``eventually_deficit_bound,
    ``uniformly_small_stopping_deficit] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL STOPPING DEFICIT IS UNIFORMLY SMALL RELATIVE TO V(z)"

end SieveNormalizedStoppingLoss
end
