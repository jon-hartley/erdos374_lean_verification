import SieveProfileStaircase

/-! Finite row-wise bounds imply a uniform actual profile refinement.
The finite threshold intersection precedes both the cutoff and the level. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Filter
open scoped BigOperators
namespace SieveProfileRowRefinement
open SieveProfileStaircase SieveEventualProfile SieveStoppingTwoStep

/-- A common threshold for all ninety rows turns the scalar row bounds
into one transfer bound on the entire bounded parameter interval. -/
theorem row_transfer (v w : ℕ → ℝ)
    (hd : ∀ j < 90, 0 ≤ w j-w (j+1)) (hterminal : w 90=0)
    (hrows : ∀ i < 90, ∃ B : ℝ, 2 ≤ B ∧ ∀ z T : ℝ,
      B ≤ z → z^2 ≤ T → left i ≤ log T/log z →
      forcing T z+operator (fun T z => profile 90 v (log T/log z)) T z ≤ w i) :
    ∃ B : ℝ, 2 ≤ B ∧ ∀ z T : ℝ, B ≤ z → z^2 ≤ T → log T/log z < 20 →
      forcing T z+operator (fun T z => profile 90 v (log T/log z)) T z ≤
        profile 90 w (log T/log z) := by
  have he : ∀ᶠ z : ℝ in atTop, ∀ i ∈ Finset.range 90, ∀ T : ℝ,
      z^2 ≤ T → left i ≤ log T/log z →
      forcing T z+operator (fun T z => profile 90 v (log T/log z)) T z ≤ w i := by
    apply (eventually_all_finset (Finset.range 90)).mpr
    intro i hi
    obtain ⟨B, _hB, hb⟩ := hrows i (Finset.mem_range.mp hi)
    filter_upwards [eventually_ge_atTop B] with z hz
    exact fun T hT hr => hb z T hz hT hr
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp he
  refine ⟨max 2 B₀, le_max_left _ _, ?_⟩
  intro z T hz hT hr20
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hz
  have hr2 := SieveStoppingArithmeticContraction.parameter_ge_two T z hz2 hT
  obtain ⟨i, hi, hl, hu⟩ := grid_cover _ hr2 hr20
  exact (hB₀ z ((le_max_right _ _).trans hz) i (Finset.mem_range.mpr hi) T hT hl).trans
    (profile_lower 90 i w (by omega) hd hterminal _ hu)

/-- Any fixed finite number of valid row transitions gives the actual
eventual profile. The iteration count is chosen before its final threshold. -/
theorem row_refinement (steps : ℕ) (v : ℕ → ℕ → ℝ)
    (hseed : EventualProfile (profile 90 (v 0)))
    (hd : ∀ n ≤ steps, ∀ j < 90, 0 ≤ v n j-v n (j+1))
    (hterminal : ∀ n ≤ steps, v n 90=0)
    (hrows : ∀ n < steps, ∀ i < 90, ∃ B : ℝ, 2 ≤ B ∧ ∀ z T : ℝ,
      B ≤ z → z^2 ≤ T → left i ≤ log T/log z →
      forcing T z+operator (fun T z => profile 90 (v n) (log T/log z)) T z ≤ v (n+1) i) :
    EventualProfile (profile 90 (v steps)) := by
  apply bounded_refinement steps 20 (fun n => profile 90 (v n)) hseed
  · intro n hn r _hr
    exact profile_nonneg 90 (v n) (hd n (by omega)) r
  · intro n hn r hr
    exact profile_tail 90 (v (n+1)) (hd (n+1) (by omega)) r hr
  · intro n hn
    exact row_transfer (v n) (v (n+1)) (hd (n+1) (by omega))
      (hterminal (n+1) (by omega)) (hrows n hn)

/-- The ten-step instance used by the finite certificate. -/
theorem ten_step (v : ℕ → ℕ → ℝ)
    (hseed : EventualProfile (profile 90 (v 0)))
    (hd : ∀ n ≤ 10, ∀ j < 90, 0 ≤ v n j-v n (j+1))
    (hterminal : ∀ n ≤ 10, v n 90=0)
    (hrows : ∀ n < 10, ∀ i < 90, ∃ B : ℝ, 2 ≤ B ∧ ∀ z T : ℝ,
      B ≤ z → z^2 ≤ T → left i ≤ log T/log z →
      forcing T z+operator (fun T z => profile 90 (v n) (log T/log z)) T z ≤ v (n+1) i) :
    EventualProfile (profile 90 (v 10)) :=
  row_refinement 10 v hseed hd hterminal hrows

run_cmd do
  for decl in [``row_transfer, ``row_refinement, ``ten_step] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FINITE ROW THRESHOLDS LIFT TO ACTUAL EVENTUAL STAIRCASE REFINEMENT"

end SieveProfileRowRefinement
end
