import PositiveSharpPrimeLower
import PositiveSharpErrorMeasure

/-! An actual prime-existence criterion on the moving backward windows.
Being outside the actual error bad set and a bound on the literal signed
remainder are explicit premises. This file does not estimate that remainder
or prove that the bad set is small. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace PositiveSharpPrimeCriterion
open PositiveSharpResidual PositiveSharpBoxedCount PositiveSharpErrorMeasure
open PositiveSharpMovingWindow SieveWeightedScalarBudget SieveStoppingExpansion

theorem eventually_prime_card_pos_of_error_bounds :
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀ s : ℝ, 0<s → s<s₀ →
      ∃ X₀ : ℝ, 1<X₀ ∧ ∀ X≥X₀, ∀ Y x : ℝ,
      0<Y → Y≤X/4 → X≤x → x≤2*X →
      x ∉ badSet X Y (1/2000) →
      signedRemainder X s x (x*Y/X)/(x*Y/X)≤(1/2000)/Real.log X →
      0<(FiniteSieveWindow.primeWindow (x-x*Y/X) x).card := by
  obtain ⟨s₀,hs₀,hs1,hb⟩ := PositiveSharpPrimeLower.eventually_prime_lower_with_errors
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss
  obtain ⟨X₀,hX₀,hcount⟩ := hb s hs hss
  refine ⟨X₀,hX₀,?_⟩
  intro X hXX Y x hY hYX hx1 hx2 hgood hrem
  have hX : 1<X := hX₀.trans_le hXX
  have hXp : 0<X := by linarith
  have hwindow := window_size_bounds X Y x hXp hY.le ⟨hx1,hx2⟩
  have hy : 0<x*Y/X := div_pos (mul_pos (hXp.trans_le hx1) hY) hXp
  have hyupper : x*Y/X≤X/2 := by linarith [hwindow.2]
  have herr := outside_badSet X Y (1/2000) x ⟨hx1,hx2⟩ hgood
  have hV : 0≤primeEuler (X^alpha s) := (SieveEulerRatio.euler_pos _).le
  have hlo := hcount X hXX x (x*Y/X) hx1 hx2 hy hyupper
  have hbudget : (1/1000:ℝ)/Real.log X=
      (1/2000)/Real.log X+(1/2000)/Real.log X := by ring
  have hratio : 0<((FiniteSieveWindow.primeWindow (x-x*Y/X) x).card:ℝ)/(x*Y/X) := by
    linarith
  have hcard : (0:ℝ)<(FiniteSieveWindow.primeWindow (x-x*Y/X) x).card := by
    have hh := (lt_div_iff₀ hy).mp hratio
    simpa only [zero_mul] using hh
  exact_mod_cast hcard

theorem eventually_prime_of_error_bounds :
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀ s : ℝ, 0<s → s<s₀ →
      ∃ X₀ : ℝ, 1<X₀ ∧ ∀ X≥X₀, ∀ Y x : ℝ,
      0<Y → Y≤X/4 → X≤x → x≤2*X →
      x ∉ badSet X Y (1/2000) →
      signedRemainder X s x (x*Y/X)/(x*Y/X)≤(1/2000)/Real.log X →
      ∃ p : ℕ, p.Prime ∧ x-x*Y/X<(p:ℝ) ∧ (p:ℝ)≤x := by
  obtain ⟨s₀,hs₀,hs1,hb⟩ := eventually_prime_card_pos_of_error_bounds
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss
  obtain ⟨X₀,hX₀,hcount⟩ := hb s hs hss
  refine ⟨X₀,hX₀,?_⟩
  intro X hXX Y x hY hYX hx1 hx2 hgood hrem
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (hcount X hXX Y x hY hYX hx1 hx2 hgood hrem)
  obtain ⟨hpwindow,hprime⟩ := Finset.mem_filter.mp hp
  have hXp : 0<X := by linarith [hX₀.trans_le hXX]
  have hwindow := window_size_bounds X Y x hXp hY.le ⟨hx1,hx2⟩
  have hl : 0≤x-x*Y/X := by linarith [hwindow.2]
  have hlr : x-x*Y/X≤x := by linarith [hwindow.1]
  exact ⟨p,hprime,(SieveDivisorWindow.mem_window_iff _ _ hl hlr p).mp hpwindow⟩

run_cmd do
  for decl in [``eventually_prime_card_pos_of_error_bounds, ``eventually_prime_of_error_bounds] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL MOVING-WINDOW PRIME EXISTS OUTSIDE ERROR BAD SET IF SIGNED REMAINDER IS SMALL"
end PositiveSharpPrimeCriterion
end
