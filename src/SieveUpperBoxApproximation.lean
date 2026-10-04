import SieveUpperNormalizedStoppingLoss
import SieveUpperNormalizedOuterCollisions
import SieveUpperBoundaryComparison
import SieveUpperReferenceCollisionBound
import SieveUpperCertified

/-! The actual all-length upper boxed main term is bounded by the ordinary
full upper selector with a vanishing normalized error. All four analytic
error inputs are discharged. Arithmetic floor remainders remain unestimated. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real Filter
open scoped Topology
namespace SieveUpperBoxApproximation
open SieveStoppingExpansion

theorem uniformly_le_fullUpper (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D →
          SieveUpperBoxWindow.mainTerm D s z ≤
            SieveFullCutoffTransfer.fullUpper D z+ε*primeEuler z := by
  obtain ⟨sS, hsS, hsSHalf, hstop⟩ :=
    SieveUpperNormalizedStoppingLoss.uniformly_small_stopping_excess (ε/4) (by linarith)
  obtain ⟨sC, hsC, _, hcollision⟩ :=
    SieveUpperNormalizedOuterCollisions.uniformly_small_ideal_gap (ε/4) (by linarith)
  obtain ⟨sB, hsB, _, hboundary⟩ :=
    SieveUpperBoundaryComparison.uniformly_small_boundary_gap (ε/4) (by linarith)
  obtain ⟨sR, hsR, _, hreference⟩ :=
    SieveUpperReferenceCollisionBound.uniformly_small_reference_difference (ε/4) (by linarith)
  refine ⟨min sS (min sC (min sB sR)), lt_min hsS (lt_min hsC (lt_min hsB hsR)),
    (min_le_left _ _).trans hsSHalf, ?_⟩
  intro s hs hss
  have hsS' : s < sS := hss.trans_le (min_le_left _ _)
  have hsC' : s < sC := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsB' : s ≤ sB :=
    (hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).le
  have hsR' : s ≤ sR :=
    (hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).le
  obtain ⟨DS, hDS, hS⟩ := hstop s hs hsS'
  obtain ⟨DC, _, hC⟩ := hcollision s hs hsC'
  obtain ⟨DB, _, hB⟩ := hboundary s hs hsB'
  obtain ⟨DR, _, hR⟩ := hreference s hs hsR'
  refine ⟨max DS (max DC (max DB DR)), hDS.trans_le (le_max_left _ _), ?_⟩
  intro D hD z hu hz
  have hDS' : DS ≤ D := (le_max_left _ _).trans hD
  have hDC' : DC ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDB' : DB ≤ D :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have hDR' : DR ≤ D :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have hstop' := hS D hDS' z hu hz
  have hcollision' := hC D hDC' z hu hz
  have hboundary' := hB D hDB' z hu hz
  have hreference' := (abs_le.mp (hR D hDR' z hu hz)).1
  have hfull : SieveUpperPoolReference.reference D s z ≤
      SieveFullCutoffTransfer.fullUpper D z := by
    rw [SieveUpperPoolReference.reference_eq_euler_mul_upperLarge]
    exact SieveFullCutoffTransfer.euler_mul_upperLarge_le_fullUpper D s z hu
  unfold SieveUpperModelLoss.excess at hstop'
  linarith

theorem uniformly_mainTerm_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D → z^3 ≤ D →
          SieveUpperBoxWindow.mainTerm D s z ≤ (452/375+ε)*primeEuler z := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := uniformly_le_fullUpper ε hε
  obtain ⟨Z, _, hupper⟩ := SieveUpperCertified.eventual_full_upper
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨DB, hDB, hB⟩ := hb s hs hss
  obtain ⟨DZ, hZ⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (sq_pos_of_pos hs)).eventually_ge_atTop Z)
  refine ⟨max DB DZ, hDB.trans_le (le_max_left _ _), ?_⟩
  intro D hD z hu hz hcubic
  have hDz : Z ≤ z := (hZ D ((le_max_right _ _).trans hD)).trans hu
  have hbox := hB D ((le_max_left _ _).trans hD) z hu hz
  have hordinary := hupper z D hDz hcubic
  nlinarith

/-- The actual boxed prime-window bound still contains its exact remainder. -/
theorem uniformly_prime_window_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D → z^3 ≤ D →
        ∀ L R : ℝ, 0 ≤ L → L ≤ R → z ≤ L →
          ((FiniteSieveWindow.primeWindow L R).card : ℝ) ≤
            (R-L)*((452/375+ε)*primeEuler z)+SieveUpperBoxWindow.remainder D s z L R := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := uniformly_mainTerm_upper ε hε
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨D₀, hD₀, hB⟩ := hb s hs hss
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD z hu hz hcubic L R hL hLR hzL
  have hcount := SieveUpperBoxWindow.prime_count_le D s z
    (hD₀.trans_le hD) hs hz hu L R hL hLR hzL
  have hmass := mul_le_mul_of_nonneg_left (hB D hD z hu hz hcubic) (sub_nonneg.mpr hLR)
  linarith

run_cmd do
  for decl in [``uniformly_le_fullUpper, ``uniformly_mainTerm_upper,
      ``uniformly_prime_window_upper] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL BOXED UPPER MAIN TERM BOUNDED; FULL ARITHMETIC REMAINDER REMAINS"
end SieveUpperBoxApproximation
end
