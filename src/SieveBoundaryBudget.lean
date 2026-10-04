import SieveBoxLength

/-! Scalar normalization of the two marked cubic-boundary strip estimates.
The tuple localization and deletion estimates are separate mathematical inputs;
this module proves the length, normalization, and uniform parameter budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real

namespace SieveBoundaryBudget

def stripMassBound (D s : ℝ) : ℝ := s^7/3 + 10/(s^2*log D)
def budget (D s : ℝ) : ℝ := (10/3)*s + 100/(s^8*log D)

theorem stripMassBound_nonneg (D s : ℝ) (hD : 1 < D) (hs : 0 < s) :
    0 ≤ stripMassBound D s := by
  have hl : 0 < log D := log_pos hD
  unfold stripMassBound
  positivity

theorem budget_nonneg (D s : ℝ) (hD : 1 < D) (hs : 0 < s) :
    0 ≤ budget D s := by
  have hl : 0 < log D := log_pos hD
  unfold budget
  positivity

theorem cutoff_le (s : ℝ) (hs : 0 < s) (hsHalf : s ≤ 1/2) :
    (SieveBoxLength.cutoff s : ℝ) ≤ 5/(4*s^2) := by
  have hs2 : 0 < s^2 := sq_pos_of_pos hs
  have hsq : s^2 ≤ 1/4 := by nlinarith
  have hf := Nat.floor_le (show 0 ≤ 1/s^2 by positivity)
  have hh : 1/s^2+1 ≤ 5/(4*s^2) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*s^2)).mpr
    field_simp
    nlinarith
  unfold SieveBoxLength.cutoff
  push_cast
  exact (add_le_add hf le_rfl).trans hh

/-- A real comparison form. Nonnegativity of R is essential when squaring
its upper bound; for the actual Euler ratio it follows from positivity. -/
theorem normalization_le (D s L R : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hL : L ≤ 5/(4*s^2)) (hR0 : 0 ≤ R) (hR : R ≤ 2/s^2) :
    2*L*stripMassBound D s*R^2 ≤ budget D s := by
  have hδ := stripMassBound_nonneg D s hD hs
  have hR2 : R^2 ≤ (2/s^2)^2 := pow_le_pow_left₀ hR0 hR 2
  have hs0 : s ≠ 0 := hs.ne'
  have hl0 : log D ≠ 0 := (log_pos hD).ne'
  calc
    _ ≤ 2*(5/(4*s^2))*stripMassBound D s*R^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by norm_num)) hδ)
        (sq_nonneg R)
    _ ≤ 2*(5/(4*s^2))*stripMassBound D s*(2/s^2)^2 :=
      mul_le_mul_of_nonneg_left hR2 (by positivity)
    _ = budget D s := by
      unfold stripMassBound budget
      field_simp
      ring

theorem cutoff_normalization_le (D s R : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hsHalf : s ≤ 1/2) (hR0 : 0 ≤ R) (hR : R ≤ 2/s^2) :
    2*(SieveBoxLength.cutoff s : ℝ)*stripMassBound D s*R^2 ≤ budget D s :=
  normalization_le D s _ R hD hs (cutoff_le s hs hsHalf) hR0 hR

/-- The parameter s is fixed before selecting the level threshold. -/
theorem eventually_budget_le (ε s : ℝ) (hε : 0 < ε) (hs : 0 < s)
    (hsmall : (10/3)*s ≤ ε/2) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → budget D s ≤ ε := by
  have hs8 : 0 < s^8 := pow_pos hs 8
  let D₀ := exp (200/(ε*s^8))
  have hD₀ : 1 < D₀ := by
    dsimp [D₀]
    exact one_lt_exp_iff.mpr (by positivity)
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD
  have hD1 : 1 < D := hD₀.trans_le hD
  have hlD : 0 < log D := log_pos hD1
  have hlog : 200/(ε*s^8) ≤ log D := by
    have hh := log_le_log (exp_pos (200/(ε*s^8))) hD
    simpa only [D₀, log_exp] using hh
  have hm : 200 ≤ log D*(ε*s^8) :=
    (div_le_iff₀ (mul_pos hε hs8)).mp hlog
  have htail : 100/(s^8*log D) ≤ ε/2 := by
    apply (div_le_iff₀ (mul_pos hs8 hlD)).mpr
    nlinarith
  unfold budget
  linarith

/-- Uniform smallness: epsilon chooses s₀, then each fixed s chooses D₀. -/
theorem uniformly_small_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → budget D s ≤ ε := by
  refine ⟨min (1/2) (3*ε/20), lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  intro s hs hss
  apply eventually_budget_le ε s hε hs
  have hh := hss.trans (min_le_right (1/2) (3*ε/20))
  nlinarith

/-- All Euler ratios satisfying the proved scalar cap share the same level
threshold. No strip-family estimate is assumed to be proved in this module. -/
theorem uniformly_small_normalization (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ R : ℝ,
        0 ≤ R → R ≤ 2/s^2 →
          2*(SieveBoxLength.cutoff s : ℝ)*stripMassBound D s*R^2 ≤ ε := by
  obtain ⟨s₀, hs₀, hsHalf, hbudget⟩ := uniformly_small_budget ε hε
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨D₀, hD₀, hb⟩ := hbudget s hs hss
  refine ⟨D₀, hD₀, fun D hD R hR0 hR => ?_⟩
  exact (cutoff_normalization_le D s R (hD₀.trans_le hD) hs (hss.trans hsHalf) hR0 hR).trans
    (hb D hD)

run_cmd do
  for decl in [``stripMassBound_nonneg, ``budget_nonneg, ``cutoff_le,
    ``normalization_le, ``cutoff_normalization_le, ``eventually_budget_le,
    ``uniformly_small_budget, ``uniformly_small_normalization] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "CUBIC BOUNDARY SCALAR BUDGET AND UNIFORM THRESHOLDS PASSED"

end SieveBoundaryBudget
end
