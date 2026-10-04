import SieveFullCutoffTransfer
import SieveReferenceCollisionBound

/-! The actual boxed main term inherits every lower bound on the complete
prime selector, losing only the already proved vanishing boxing error. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SieveBoxedFullComparison
open SieveStoppingExpansion

theorem lower_bound_of_pool_error (D s z ε : ℝ) (hu : D^(s^2) ≤ z)
    (he : |SieveBoxedWindow.mainTerm D s z-SievePoolReference.reference D s z|
      ≤ ε*primeEuler z) :
    SieveFullCutoffTransfer.fullLower D z-ε*primeEuler z ≤
      SieveBoxedWindow.mainTerm D s z := by
  have hcut := SieveFullCutoffTransfer.fullLower_le_reference D s z hu
  have hlow := (abs_le.mp he).1
  linarith

theorem uniformly_above_full_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D →
          SieveFullCutoffTransfer.fullLower D z-ε*primeEuler z ≤
            SieveBoxedWindow.mainTerm D s z := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ :=
    SieveReferenceCollisionBound.uniformly_approximate_pool_reference ε hε
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨D₀, hD₀, hbound⟩ := hb s hs hss
  exact ⟨D₀, hD₀, fun D hD z hu hz =>
    lower_bound_of_pool_error D s z ε hu (hbound D hD z hu hz)⟩

run_cmd do
  for decl in [``lower_bound_of_pool_error, ``uniformly_above_full_lower] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL BOXED MAIN TERM BOUNDED BELOW BY FULL PRIME SELECTOR MINUS VANISHING ERROR"
end SieveBoxedFullComparison
end
