import SieveProfileCertificateBridge
import SieveProfileRowRefinement
import SieveProfileUniformBound
import SieveBoxedPositive

/-! Unconditional sharpened first lower sieve term from ten exact profile
iterations. Other signed contributions and the final prime count remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real Filter
open scoped BigOperators
namespace SieveProfileMainTerm
open ProfileCertificateIndexed SieveProfileCertificateBridge
open SieveStoppingExpansion SieveStoppingTwoStep

theorem certified_differences (n : ℕ) (hn : n ≤ 10) (j : ℕ) (hj : j < 90) :
    0 ≤ value n j-value n (j+1) :=
  coefficient_nonneg ⟨n, by omega⟩ ⟨j, hj⟩

theorem certified_terminal (n : ℕ) (hn : n ≤ 10) : value n 90 = 0 :=
  value_terminal ⟨n, by omega⟩

theorem eventual_certified_profile : SieveEventualProfile.EventualProfile (certifiedProfile 10) := by
  apply SieveProfileRowRefinement.ten_step value
  · apply SieveProfileStaircase.seed_profile (value 0)
      (certified_differences 0 (by norm_num)) (certified_terminal 0 (by norm_num))
    intro i hi
    exact initial_rational_bound ⟨i, hi⟩
  · exact certified_differences
  · exact certified_terminal
  · intro n hn i hi
    exact actual_row ⟨n, hn⟩ ⟨i, hi⟩

theorem eventual_exact_target_bound :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
      log T/log z = (105/26:ℝ) →
      normalizedLower T z ≤ (53589103/1000000000:ℝ) := by
  obtain ⟨Z, hZ, hb⟩ := eventual_certified_profile
  refine ⟨Z, hZ, ?_⟩
  intro z T hz hT hr
  have h := hb z T hz hT
  rw [hr, certifiedProfile, SieveProfileStaircase.profile_target _
    (certified_terminal 10 (by norm_num)), final_value] at h
  exact h

theorem eventual_loss_one_sixteenth :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
      (105/26:ℝ) ≤ log T/log z → normalizedLower T z ≤ (1/16:ℝ) := by
  obtain ⟨Z, hZ, hb⟩ := eventual_certified_profile
  refine ⟨Z, hZ, ?_⟩
  intro z T hz hT hr
  have h := SieveProfileUniformBound.profile_le_target_plus_tail (value 10)
    (certified_differences 10 (by norm_num)) (certified_terminal 10 (by norm_num))
    (log T/log z) hr
  rw [final_value] at h
  have hnum : (53589103/1000000000:ℝ)+1/10000 ≤ 1/16 := by norm_num
  exact (hb z T hz hT).trans (h.trans hnum)

theorem full_lower_of_loss (T z : ℝ) (hloss : normalizedLower T z ≤ (1/16:ℝ)) :
    (15/16:ℝ)*primeEuler z ≤ SieveFullCutoffTransfer.fullLower T z := by
  have he := SieveEulerRatio.euler_pos z
  have hh := (div_le_iff₀ he).mp hloss
  rw [SieveFullLowerPositive.fullLower_eq_euler_sub_loss]
  linarith

theorem eventual_full_lower :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
      (105/26:ℝ) ≤ log T/log z →
      (15/16:ℝ)*primeEuler z ≤ SieveFullCutoffTransfer.fullLower T z := by
  obtain ⟨Z, hZ, hb⟩ := eventual_loss_one_sixteenth
  exact ⟨Z, hZ, fun z T hz hT hr => full_lower_of_loss T z (hb z T hz hT hr)⟩

theorem uniformly_mainTerm_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z^2 ≤ D → (105/26:ℝ) ≤ log D/log z →
          (15/16-ε)*primeEuler z ≤ SieveBoxedWindow.mainTerm D s z := by
  obtain ⟨Z, hZ, hfull⟩ := eventual_full_lower
  obtain ⟨s₀, hs₀, hsHalf, hbox⟩ := SieveBoxedFullComparison.uniformly_above_full_lower ε hε
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
  nlinarith

theorem mainTerm_at_first_cutoff (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        (15/16-ε)*primeEuler (D^(26/105:ℝ)) ≤
          SieveBoxedWindow.mainTerm D s (D^(26/105:ℝ)) := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := uniformly_mainTerm_lower ε hε
  refine ⟨min s₀ (1/3), lt_min hs₀ (by norm_num), (min_le_left _ _).trans hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨D₀, hD₀, hbound⟩ := hb s hs (hss.trans_le (min_le_left _ _))
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD
  obtain ⟨hu, hlevel, hr⟩ := SieveBoxedPositive.first_cutoff_conditions D s
    (hD₀.trans_le hD) hs (hss.le.trans (min_le_right _ _))
  exact hbound D hD _ hu hlevel hr

run_cmd do
  for decl in [``certified_differences, ``certified_terminal, ``eventual_certified_profile,
    ``eventual_exact_target_bound, ``eventual_loss_one_sixteenth, ``full_lower_of_loss,
    ``eventual_full_lower, ``uniformly_mainTerm_lower, ``mainTerm_at_first_cutoff] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL FIRST LOWER SIEVE MAIN TERM: AT LEAST (15/16-EPSILON)*V"
end SieveProfileMainTerm
end
