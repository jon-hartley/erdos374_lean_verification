import PositiveSharpBoxedCount
import PositiveSharpSourceBound

/-! Actual prime-window lower bound with every missing arithmetic error
explicit. This is an unconditional inequality, not a proved positive count. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace PositiveSharpPrimeLower
open Real PositiveSharpResidual PositiveSharpBoxedCount
open PositiveSharpSieveDecomposition SieveWeightedScalarBudget SieveStoppingExpansion

theorem eventually_prime_lower_with_errors :
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀ s : ℝ, 0<s → s<s₀ →
      ∃ X₀ : ℝ, 1<X₀ ∧ ∀ X≥X₀, ∀ x y : ℝ,
      X≤x → x≤2*X → 0<y → y≤X/2 →
      (3/100:ℝ)*primeEuler (X^alpha s)+(1/1000)/log X-
        residualAbs X x y-deletionTotal X x y-signedRemainder X s x y/y <
          ((FiniteSieveWindow.primeWindow (x-y) x).card:ℝ)/y := by
  obtain ⟨s₀,hs₀,hs1,hb⟩ := PositiveSharpSourceBound.eventually_signed_source_with_errors
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss
  obtain ⟨A,hA,hsource⟩ := hb s hs hss
  refine ⟨max A (max 8 (exp 1000)), hA.trans_le (le_max_left _ _), ?_⟩
  intro X hX x y hx1 hx2 hy1 hy2
  have hXA : A≤X := (le_max_left _ _).trans hX
  have hX8 : 8≤X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hlog : 1000≤log X := by
    simpa only [log_exp] using log_le_log (exp_pos (1000:ℝ))
      ((le_max_right _ _).trans ((le_max_right _ _).trans hX))
  have hsmax : s≤1/1000 := hss.le.trans hs1
  have hS2 : ∀ p∈largePrimes X, p.Prime ∧ X^(9/35:ℝ)≤(p:ℝ) ∧
      (p:ℝ)≤sqrt (2*X) := fun p hp => large_band_bounds X p hp
  have hS3 : ∀ p∈smallPrimes X s, p.Prime ∧ X^alpha s≤(p:ℝ) ∧
      (p:ℝ)≤X^(9/35:ℝ) := by
    intro p hp
    have hh := small_band_bounds X s p hp
    exact ⟨hh.1,hh.2.1,hh.2.2.le⟩
  have hm := hsource X hXA x y hx1 hx2 hy1 hy2 (largePrimes X) (smallPrimes X s) hS2 hS3
  change _ < signedMainTerm X s+(PositiveSharpBuchstab.sourceTerm X s x y:ℝ)/y at hm
  have hc := PositiveSharpBoxedCount.prime_count_lower X s x y hX8 hs hsmax hlog
    ⟨hx1,hx2⟩ ⟨hy1,hy2⟩
  have hd := div_le_div_of_nonneg_right hc hy1.le
  have heq : (y*signedMainTerm X s+(PositiveSharpBuchstab.sourceTerm X s x y:ℝ)-
      signedRemainder X s x y)/y = signedMainTerm X s+
      (PositiveSharpBuchstab.sourceTerm X s x y:ℝ)/y-signedRemainder X s x y/y := by
    field_simp
  rw [heq] at hd
  linarith

run_cmd do
  for ax in (← Lean.collectAxioms ``eventually_prime_lower_with_errors) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in eventually_prime_lower_with_errors"
  Lean.logInfo "ACTUAL PRIME-WINDOW LOWER BOUND; MIXED FLUCTUATION AND SIGNED REMAINDER STILL UNBOUNDED"
end PositiveSharpPrimeLower
end
