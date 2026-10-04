import SieveNormalizedStoppingLoss
import SieveNormalizedCollisions

/-! The actual boxed main term approximates its strict-profile ideal on the
Euler-product scale. Both stopping and same-band collision errors are proved
small. No positivity assertion about the strict ideal is used or supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace SieveActualMainTermApproximation
open SieveStoppingExpansion SieveNormalizedCollisions

/-- Exact decomposition into the two genuine nonnegative error terms. -/
theorem gap_exact (D s z : ℝ) :
    strictIdeal D s z - SieveBoxedWindow.mainTerm D s z =
      primeEuler (D^(s^2)) * SieveBoxCollisions.collisionMass false D s z +
        SieveModelLoss.deficit D s z := by
  rw [mainTerm_strict_exact, SieveModelLoss.deficit_exact]
  ring

theorem gap_nonneg (D s z : ℝ) :
    0 ≤ strictIdeal D s z - SieveBoxedWindow.mainTerm D s z := by
  rw [gap_exact]
  exact add_nonneg
    (mul_nonneg (SieveEulerRatio.euler_pos _).le
      (SieveBoxCollisions.collisionMass_nonneg false D s z))
    (SieveModelLoss.deficit_nonneg D s z)

/-- The same small-parameter and large-level thresholds control both actual
errors, uniformly in the upper prime cutoff. -/
theorem uniformly_small_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D →
          strictIdeal D s z - SieveBoxedWindow.mainTerm D s z ≤ ε * primeEuler z := by
  obtain ⟨sS, hsS, hsSHalf, hstop⟩ :=
    SieveNormalizedStoppingLoss.uniformly_small_stopping_deficit (ε/2) (by linarith)
  obtain ⟨sC, hsC, _, hcoll⟩ := uniformly_small_collision (ε/2) (by linarith)
  refine ⟨min sS sC, lt_min hsS hsC, (min_le_left _ _).trans hsSHalf, ?_⟩
  intro s hs hss
  obtain ⟨DS, hDS, hstopD⟩ := hstop s hs (hss.trans_le (min_le_left _ _))
  obtain ⟨DC, hDC, hcollD⟩ := hcoll s hs (hss.trans_le (min_le_right _ _))
  refine ⟨max DS DC, hDS.trans_le (le_max_left _ _), ?_⟩
  intro D hD z hu hz
  have hS := hstopD D ((le_max_left _ _).trans hD) z hu hz
  have hC := hcollD D ((le_max_right _ _).trans hD) z hu hz false
  rw [gap_exact]
  calc
    _ ≤ (ε/2)*primeEuler z + (ε/2)*primeEuler z := add_le_add hC hS
    _ = _ := by ring

/-- A two-sided approximation of the actual main term by the strict ideal.
The ideal may have either sign; this theorem does not prove a positive main term. -/
theorem uniformly_approximate_mainTerm (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D →
          strictIdeal D s z - ε * primeEuler z ≤ SieveBoxedWindow.mainTerm D s z ∧
          SieveBoxedWindow.mainTerm D s z ≤ strictIdeal D s z := by
  obtain ⟨s₀, hs₀, hsHalf, hsmall⟩ := uniformly_small_gap ε hε
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨D₀, hD₀, hbound⟩ := hsmall s hs hss
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD z hu hz
  have hh := hbound D hD z hu hz
  have hn := gap_nonneg D s z
  constructor <;> linarith

run_cmd do
  for decl in [``gap_exact, ``gap_nonneg, ``uniformly_small_gap,
    ``uniformly_approximate_mainTerm] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL BOXED MAIN TERM APPROXIMATES STRICT IDEAL RELATIVE TO V(z)"

end SieveActualMainTermApproximation
end
