import SieveProfileMainTerm

/-! Preserve the exact target bound uniformly above the target ratio by
handling the exponential-tail join separately. This improves the actual
first boxed term; no other signed main term is assumed or concluded. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Filter
namespace SieveFirstTermSharp
open ProfileCertificateIndexed SieveProfileCertificateBridge
open SieveProfileStaircase SieveProfileMainTerm
open SieveStoppingExpansion SieveStoppingTwoStep

theorem last_value : value 10 89 = (110836/1000000000:ℝ) := by
  have h : entry 10 89 = 110836 := by decide
  simp only [value, h]
  norm_num

theorem certified_profile_uniform (r : ℝ) (hr : (105/26:ℝ) ≤ r) :
    certifiedProfile 10 r ≤ (53589103/1000000000:ℝ) := by
  have hd := certified_differences 10 (by norm_num)
  have hN := certified_terminal 10 (by norm_num)
  change profile 90 (value 10) r ≤ _
  by_cases h20 : r < 20
  · have h := (SieveProfileUniformBound.staircase_antitone 90 (value 10) hd hr).trans_eq
      (SieveProfileUniformBound.staircase_target _ hN)
    simpa only [profile, SieveProfileExponentialTail.tail,
      not_le.mpr h20, ite_false, add_zero, final_value] using h
  · have h := SieveProfileUniformBound.staircase_antitone 90 (value 10) hd
      (le_of_not_gt h20)
    rw [staircase_eq 90 89 (value 10) (by norm_num) 20
      (by norm_num [left]) (by norm_num [cut]), hN, sub_zero, last_value] at h
    have ht := SieveProfileUniformBound.tail_bound r
    unfold profile
    linarith

theorem eventual_loss_sharp :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
      (105/26:ℝ) ≤ log T/log z →
      normalizedLower T z ≤ (53589103/1000000000:ℝ) := by
  obtain ⟨Z, hZ, hb⟩ := eventual_certified_profile
  exact ⟨Z, hZ, fun z T hz hT hr =>
    (hb z T hz hT).trans (certified_profile_uniform _ hr)⟩

theorem eventual_full_lower_sharp :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
      (105/26:ℝ) ≤ log T/log z →
      (946410897/1000000000:ℝ)*primeEuler z ≤
        SieveFullCutoffTransfer.fullLower T z := by
  obtain ⟨Z, hZ, hb⟩ := eventual_loss_sharp
  refine ⟨Z, hZ, ?_⟩
  intro z T hz hT hr
  have hh := (div_le_iff₀ (SieveEulerRatio.euler_pos z)).mp (hb z T hz hT hr)
  rw [SieveFullLowerPositive.fullLower_eq_euler_sub_loss]
  linarith

theorem uniformly_mainTerm_lower_sharp (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z^2 ≤ D → (105/26:ℝ) ≤ log D/log z →
          (946410897/1000000000-ε)*primeEuler z ≤
            SieveBoxedWindow.mainTerm D s z := by
  obtain ⟨Z, hZ, hfull⟩ := eventual_full_lower_sharp
  obtain ⟨s₀, hs₀, hsHalf, hbox⟩ :=
    SieveBoxedFullComparison.uniformly_above_full_lower ε hε
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨DB, hDB, hboxD⟩ := hbox s hs hss
  obtain ⟨DZ, hDZ⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (sq_pos_of_pos hs)).eventually_ge_atTop Z)
  refine ⟨max DB DZ, hDB.trans_le (le_max_left _ _), ?_⟩
  intro D hD z hu hlevel hr
  have hDz : Z ≤ D^(s^2) := hDZ D ((le_max_right _ _).trans hD)
  have hz2 : 2 ≤ z := hZ.trans (hDz.trans hu)
  have hzD : z ≤ D := by nlinarith
  have hf := hfull z D (hDz.trans hu) hlevel hr
  have hb := hboxD D ((le_max_left _ _).trans hD) z hu hzD
  nlinarith

theorem mainTerm_at_first_cutoff_sharp (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        (946410897/1000000000-ε)*primeEuler (D^(26/105:ℝ)) ≤
          SieveBoxedWindow.mainTerm D s (D^(26/105:ℝ)) := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := uniformly_mainTerm_lower_sharp ε hε
  refine ⟨min s₀ (1/3), lt_min hs₀ (by norm_num),
    (min_le_left _ _).trans hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨D₀, hD₀, hbound⟩ := hb s hs (hss.trans_le (min_le_left _ _))
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD
  obtain ⟨hu, hlevel, hr⟩ := SieveBoxedPositive.first_cutoff_conditions D s
    (hD₀.trans_le hD) hs (hss.le.trans (min_le_right _ _))
  exact hbound D hD _ hu hlevel hr

run_cmd do
  for decl in [``last_value, ``certified_profile_uniform, ``eventual_loss_sharp,
      ``eventual_full_lower_sharp, ``uniformly_mainTerm_lower_sharp,
      ``mainTerm_at_first_cutoff_sharp] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL FIRST BOXED LOWER TERM: (0.946410897-EPSILON)*V"
end SieveFirstTermSharp
end
