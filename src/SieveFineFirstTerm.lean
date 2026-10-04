import SieveUpperCertified
import SieveFirstTermSharp

/-! The certified fine profile gives an actual 122/125 lower selector
above the source target ratio, and hence its boxed approximation.
No signed remainder or positive arithmetic prime count is concluded. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
open Real Filter
open scoped BigOperators
namespace SieveFineFirstTerm
open SieveFineProfileStructure SieveStoppingExpansion SieveStoppingTwoStep

theorem staircase_le_value (v : ℕ → ℝ)
    (hd : ∀ j < 720, 0 ≤ coefficient v j) (hN : v 720 = 0)
    (i : ℕ) (hi : i ≤ 720) (r : ℝ) (hr : rowPoint i < r) :
    SieveProfileTransition.staircase (Finset.range 720) (coefficient v) cut r ≤ v i := by
  have hs := SieveProfileStaircase.suffix_sum 720 i v hi
  rw [hN, sub_zero] at hs
  rw [← hs]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i ≤ j
  · simp only [hij, ite_true]
    by_cases hrj : r ≤ cut j
    · simp only [hrj, ite_true, mul_one, coefficient, le_refl]
    · simp only [hrj, ite_false, mul_zero]
      exact hd j (Finset.mem_range.mp hj)
  · have hji : (j:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast (show j+1 ≤ i by omega)
    have hrj : ¬ r ≤ cut j := by
      unfold rowPoint at hr
      unfold cut
      linarith
    simp only [hij, hrj, ite_false, mul_zero, le_refl]

theorem target_value :
    UpperProfileCertificate.value 81 = (23941324526/1000000000000:ℝ) := by
  have h : UpperProfileCertificateData.height 81 = 23941324526 := by decide
  norm_num [UpperProfileCertificate.value, h, UpperProfileGridArithmetic.scale]

theorem last_value :
    UpperProfileCertificate.value 719 = (111701963/1000000000000:ℝ) := by
  have h : UpperProfileCertificateData.height 719 = 111701963 := by decide
  norm_num [UpperProfileCertificate.value, h, UpperProfileGridArithmetic.scale]

theorem profile_uniform (r : ℝ) (hr : (105/26:ℝ) ≤ r) :
    profile UpperProfileCertificate.value r ≤ (23941324526/1000000000000:ℝ) := by
  by_cases h20 : r < 20
  · have hh := staircase_le_value UpperProfileCertificate.value
      SieveUpperCertified.certified_differences UpperProfileCertificate.value_terminal
      81 (by norm_num) r (by unfold rowPoint; norm_num; linarith)
    simpa only [profile, SieveProfileTransition.profile, SieveProfileExponentialTail.tail,
      not_le.mpr h20, ite_false, add_zero, target_value] using hh
  · have hr20 : (20:ℝ) ≤ r := le_of_not_gt h20
    have hh := staircase_le_value UpperProfileCertificate.value
      SieveUpperCertified.certified_differences UpperProfileCertificate.value_terminal
      719 (by norm_num) r (by unfold rowPoint; norm_num; linarith)
    rw [last_value] at hh
    have ht := SieveProfileUniformBound.tail_bound r
    unfold profile SieveProfileTransition.profile
    linarith

theorem eventual_loss :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
      (105/26:ℝ) ≤ log T/log z → normalizedLower T z ≤ (3/125:ℝ) := by
  obtain ⟨Z, hZ, hb⟩ := SieveUpperCertified.eventual_lower_profile
    (1/100000:ℝ) (by norm_num)
  refine ⟨Z, hZ, ?_⟩
  intro z T hz hT hr
  have hp := profile_uniform (log T/log z) hr
  have he : exp (-(log T/log z)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hh := hb z T hz hT
  linarith

theorem eventual_full_lower :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
      (105/26:ℝ) ≤ log T/log z →
      (122/125:ℝ)*primeEuler z ≤ SieveFullCutoffTransfer.fullLower T z := by
  obtain ⟨Z, hZ, hb⟩ := eventual_loss
  refine ⟨Z, hZ, ?_⟩
  intro z T hz hT hr
  have hh := (div_le_iff₀ (SieveEulerRatio.euler_pos z)).mp (hb z T hz hT hr)
  rw [SieveFullLowerPositive.fullLower_eq_euler_sub_loss]
  linarith

theorem uniformly_mainTerm_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z^2 ≤ D → (105/26:ℝ) ≤ log D/log z →
          (122/125-ε)*primeEuler z ≤ SieveBoxedWindow.mainTerm D s z := by
  obtain ⟨Z, hZ, hfull⟩ := eventual_full_lower
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

theorem mainTerm_at_first_cutoff (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        (122/125-ε)*primeEuler (D^(26/105:ℝ)) ≤
          SieveBoxedWindow.mainTerm D s (D^(26/105:ℝ)) := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := uniformly_mainTerm_lower ε hε
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
  for decl in [``staircase_le_value, ``target_value, ``last_value, ``profile_uniform,
      ``eventual_loss, ``eventual_full_lower, ``uniformly_mainTerm_lower,
      ``mainTerm_at_first_cutoff] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FINE ACTUAL FIRST LOWER SELECTOR: 122/125; BOXED TERM UP TO EPSILON"
end SieveFineFirstTerm
end
