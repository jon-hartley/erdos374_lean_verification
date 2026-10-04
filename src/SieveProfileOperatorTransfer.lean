import SieveProfileOperatorGrid
import Mathlib.Analysis.SpecificLimits.Basic

/-! Uniform eventual transfer of a finite rectangle coefficient to the
actual accepted-prime operator. The cutoff is selected before both z and T. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Filter
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveProfileOperatorTransfer
open SieveProfileOperatorGrid SieveProfileOperatorCumulative PrimeEulerProfileIntervals

theorem gridBound_continuous (r c h : ℝ) (N : ℕ) : Continuous (gridBound r c h N) := by
  unfold gridBound binInner
  fun_prop

theorem epsilon_tendsto : Tendsto epsilon atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_log_atTop

theorem two_le_cut (z x : ℝ) (hx : 0 < x) (hz : exp (x*log 2) ≤ z) :
    2 ≤ cut z x := by
  have hl := log_le_log (exp_pos _) hz
  rw [log_exp] at hl
  calc
    (2:ℝ) = exp (log 2) := (exp_log (by norm_num : (0:ℝ) < 2)).symm
    _ ≤ exp (log z/x) := exp_le_exp.mpr ((le_div_iff₀ hx).mpr (by nlinarith))

/-- A literal finite rectangle coefficient bounds the actual cumulative
operator up to any prescribed positive error, uniformly in the parent level. -/
theorem eventually_cumulative (r c h : ℝ) (N : ℕ)
    (hr : 2 ≤ r) (hc : 2 ≤ c) (hh : 0 ≤ h) (hcover : c+2 ≤ r*edge h N)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T → r ≤ log T/log z →
      SieveStoppingTwoStep.operator (fun T z => if log T/log z ≤ c then 1 else 0) T z ≤
        h*(∑ k ∈ Finset.range N, shape c (r*edge h k-1))+δ := by
  have ht := (gridBound_continuous r c h N).continuousAt.tendsto.comp epsilon_tendsto
  have hev : ∀ᶠ z : ℝ in atTop, gridBound r c h N (epsilon z) < gridBound r c h N 0+δ :=
    ht.eventually_lt_const (by linarith)
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp hev
  let Z := max 2 (max Z₀ (max (exp ((c+1)*log 2)) (exp (edge h N*log 2))))
  refine ⟨Z, le_max_left _ _, ?_⟩
  intro z T hz hT hparam
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hz
  have hz₀ : Z₀ ≤ z := (le_max_left _ _).trans ((le_max_right _ _).trans hz)
  have hza : exp ((c+1)*log 2) ≤ z := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hz))
  have hzb : exp (edge h N*log 2) ≤ z := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hz))
  have hcut : 2 ≤ lowerCut z c := two_le_cut z (c+1) (by linarith) hza
  have hgrid : 2 ≤ cut z (edge h N) := two_le_cut z (edge h N)
    (by linarith [edge_ge_one h N hh]) hzb
  rw [operator_indicator_eq]
  exact (cumulative_grid_bound T z c r h N hz2 hT hc hr hh hparam hcover hcut hgrid).trans
    (by simpa only [gridBound_zero] using (hZ₀ z hz₀).le)

run_cmd do
  for decl in [``gridBound_continuous, ``epsilon_tendsto, ``two_le_cut,
    ``eventually_cumulative] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "UNIFORM EVENTUAL ACTUAL CUMULATIVE PROFILE TRANSFER PASSED"
end SieveProfileOperatorTransfer
end
