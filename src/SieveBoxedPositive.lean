import SieveFullLowerPositive
import SieveBoxedFullComparison

/-! Quantitative positivity of the actual boxed first sieve main term.
This does not control the other signed sieve contributions or remainders. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Filter
namespace SieveBoxedPositive
open SieveStoppingExpansion

theorem uniformly_positive_mainTerm :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z^2 ≤ D → (105/26:ℝ) ≤ log D/log z →
          primeEuler z/100 ≤ SieveBoxedWindow.mainTerm D s z := by
  obtain ⟨Z, hZ, hfull⟩ := SieveFullLowerPositive.eventual_full_lower
  obtain ⟨s₀, hs₀, hsHalf, hbox⟩ :=
    SieveBoxedFullComparison.uniformly_above_full_lower (1/100) (by norm_num)
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨DB, hDB, hboxD⟩ := hbox s hs hss
  have hev := (tendsto_rpow_atTop (sq_pos_of_pos hs)).eventually_ge_atTop Z
  obtain ⟨DZ, hDZ⟩ := eventually_atTop.mp hev
  refine ⟨max DB DZ, hDB.trans_le (le_max_left _ _), ?_⟩
  intro D hD z hu hlevel hr
  have hDz : Z ≤ D^(s^2) := hDZ D ((le_max_right _ _).trans hD)
  have hz2 : 2 ≤ z := hZ.trans (hDz.trans hu)
  have hzD : z ≤ D := by nlinarith
  have hf := hfull z D (hDz.trans hu) hlevel hr
  have hb := hboxD D ((le_max_left _ _).trans hD) z hu hzD
  linarith

theorem first_cutoff_conditions (D s : ℝ) (hD : 1 < D)
    (hs : 0 < s) (hsThird : s ≤ 1/3) :
    D^(s^2) ≤ D^(26/105:ℝ) ∧
      (D^(26/105:ℝ))^2 ≤ D ∧
        (105/26:ℝ) ≤ log D/log (D^(26/105:ℝ)) := by
  have hD0 : 0 < D := by linarith
  have hl : log D ≠ 0 := (log_pos hD).ne'
  have hs2 : s^2 ≤ (26/105:ℝ) := by nlinarith
  refine ⟨rpow_le_rpow_of_exponent_le hD.le hs2, ?_, ?_⟩
  · rw [← rpow_natCast, ← rpow_mul hD0.le]
    exact rpow_le_self_of_one_le hD.le (by norm_num)
  · rw [log_rpow hD0]
    have he : log D/((26/105:ℝ)*log D) = (105/26:ℝ) := by field_simp
    rw [he]

theorem positive_at_first_cutoff :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        primeEuler (D^(26/105:ℝ))/100 ≤
          SieveBoxedWindow.mainTerm D s (D^(26/105:ℝ)) := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := uniformly_positive_mainTerm
  refine ⟨min s₀ (1/3), lt_min hs₀ (by norm_num), (min_le_left _ _).trans hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨D₀, hD₀, hbound⟩ := hb s hs (hss.trans_le (min_le_left _ _))
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD
  obtain ⟨hu, hlevel, hr⟩ := first_cutoff_conditions D s (hD₀.trans_le hD) hs
    (hss.le.trans (min_le_right _ _))
  exact hbound D hD _ hu hlevel hr

theorem eventually_strictly_positive_at_first_cutoff :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        0 < SieveBoxedWindow.mainTerm D s (D^(26/105:ℝ)) := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := positive_at_first_cutoff
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨D₀, hD₀, hbound⟩ := hb s hs hss
  exact ⟨D₀, hD₀, fun D hD =>
    (div_pos (SieveEulerRatio.euler_pos _) (by norm_num : (0:ℝ) < 100)).trans_le (hbound D hD)⟩

run_cmd do
  for decl in [``uniformly_positive_mainTerm, ``first_cutoff_conditions,
    ``positive_at_first_cutoff, ``eventually_strictly_positive_at_first_cutoff] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL BOXED FIRST MAIN TERM POSITIVE: AT LEAST V(D^(26/105))/100"
end SieveBoxedPositive
end
