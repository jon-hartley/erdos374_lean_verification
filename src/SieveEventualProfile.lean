import SieveEventualStoppingBound

/-! Finite-profile refinement for the actual stopping recurrence. The
threshold is selected before all levels and cutoffs; bounded recursive
cutoffs are handled by exact saturation. Analytic transfer bounds are
explicit inputs to the generic refinement theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real
open scoped BigOperators
namespace SieveEventualProfile
open SieveStoppingTwoStep

def EventualProfile (φ : ℝ → ℝ) : Prop :=
  ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
    normalizedLower T z ≤ φ (log T/log z)

theorem profile_mono (φ ψ : ℝ → ℝ) (hφ : EventualProfile φ)
    (hφψ : ∀ r : ℝ, 2 ≤ r → φ r ≤ ψ r) : EventualProfile ψ := by
  obtain ⟨Z, hZ, hb⟩ := hφ
  exact ⟨Z, hZ, fun z T hz hT => (hb z T hz hT).trans
    (hφψ _ (SieveStoppingArithmeticContraction.parameter_ge_two T z (hZ.trans hz) hT))⟩

theorem initial_profile : EventualProfile (fun r => 91*exp (-r)) :=
  SieveEventualStoppingBound.eventually_ninety_one

theorem operator_le_of_children (T z : ℝ) (φ : ℝ → ℝ)
    (hchild : ∀ p ∈ SieveSmallWeights.pool z, ∀ q ∈ SieveSmallWeights.pool (p:ℝ),
      (q:ℝ)^3 < T/(p:ℝ) →
      normalizedLower ((T/(p:ℝ))/(q:ℝ)) (q:ℝ) ≤
        φ (log ((T/(p:ℝ))/(q:ℝ))/log (q:ℝ))) :
    operator normalizedLower T z ≤ operator (fun T z => φ (log T/log z)) T z := by
  unfold operator
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  split_ifs with hg
  · apply mul_le_mul_of_nonneg_left (hchild p hp q hq hg)
    exact div_nonneg (mul_nonneg (mul_nonneg
      (inv_nonneg.mpr (Nat.cast_nonneg p)) (inv_nonneg.mpr (Nat.cast_nonneg q)))
      (SieveEulerRatio.euler_pos _).le) (SieveEulerRatio.euler_pos z).le
  · exact le_rfl

/-- A single threshold makes every accepted child either satisfy the
previous profile or have exactly zero stopping loss. -/
theorem eventually_operator_le (φ : ℝ → ℝ)
    (hφ0 : ∀ r : ℝ, 2 ≤ r → 0 ≤ φ r) (hφ : EventualProfile φ) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
      operator normalizedLower T z ≤ operator (fun T z => φ (log T/log z)) T z := by
  obtain ⟨Y, hY, hb⟩ := hφ
  let Z := max 2 (Y*SieveFiniteBase.saturationLevel Y)
  refine ⟨Z, le_max_left _ _, ?_⟩
  intro z T hz hT
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hz
  apply operator_le_of_children T z φ
  intro p hp q hq hg
  obtain ⟨hq2, hchildlevel⟩ := SieveStoppingDecay.accepted_child_level T p q hq hg
  by_cases hqY : Y ≤ (q:ℝ)
  · exact hb (q:ℝ) ((T/(p:ℝ))/(q:ℝ)) hqY hchildlevel
  · rw [SieveEventualStoppingBound.small_child_saturated T z Y p q hY
      ((le_max_right _ _).trans hz) hz2 hT hp hq (le_of_not_ge hqY)]
    exact hφ0 _ (SieveStoppingArithmeticContraction.parameter_ge_two _ _ hq2 hchildlevel)

theorem refine_profile (φ ψ : ℝ → ℝ)
    (hφ0 : ∀ r : ℝ, 2 ≤ r → 0 ≤ φ r) (hφ : EventualProfile φ)
    (htransfer : ∃ B : ℝ, 2 ≤ B ∧ ∀ z T : ℝ, B ≤ z → z^2 ≤ T →
      forcing T z + operator (fun T z => φ (log T/log z)) T z ≤ ψ (log T/log z)) :
    EventualProfile ψ := by
  obtain ⟨Y, hY, hchild⟩ := eventually_operator_le φ hφ0 hφ
  obtain ⟨B, hB, hb⟩ := htransfer
  refine ⟨max Y B, hY.trans (le_max_left _ _), ?_⟩
  intro z T hz hT
  rw [normalizedLower_two_step]
  exact (add_le_add le_rfl (hchild z T ((le_max_left _ _).trans hz) hT)).trans
    (hb z T ((le_max_right _ _).trans hz) hT)

theorem finite_refinement (φ : ℕ → ℝ → ℝ)
    (hzero : EventualProfile (φ 0))
    (hnonneg : ∀ n r, 2 ≤ r → 0 ≤ φ n r)
    (hstep : ∀ n : ℕ, ∃ B : ℝ, 2 ≤ B ∧ ∀ z T : ℝ, B ≤ z → z^2 ≤ T →
      forcing T z + operator (fun T z => φ n (log T/log z)) T z ≤ φ (n+1) (log T/log z))
    (n : ℕ) : EventualProfile (φ n) := by
  induction n with
  | zero => exact hzero
  | succ n ih => exact refine_profile (φ n) (φ (n+1)) (hnonneg n) ih (hstep n)

/-- Only the bounded profile range needs a new transfer. At larger ratios
the already proved exponential envelope is reused, even if the joined
profile is discontinuous or increases at the joining point. -/
theorem refine_profile_below (H : ℝ) (φ ψ : ℝ → ℝ)
    (hφ0 : ∀ r : ℝ, 2 ≤ r → 0 ≤ φ r) (hφ : EventualProfile φ)
    (htail : ∀ r : ℝ, H ≤ r → 91*exp (-r) ≤ ψ r)
    (htransfer : ∃ B : ℝ, 2 ≤ B ∧ ∀ z T : ℝ, B ≤ z → z^2 ≤ T →
      log T/log z < H →
      forcing T z + operator (fun T z => φ (log T/log z)) T z ≤ ψ (log T/log z)) :
    EventualProfile ψ := by
  obtain ⟨Y, hY, hchild⟩ := eventually_operator_le φ hφ0 hφ
  obtain ⟨B, hB, hb⟩ := htransfer
  obtain ⟨E, hE, hexp⟩ := initial_profile
  refine ⟨max (max Y B) E, hE.trans (le_max_right _ _), ?_⟩
  intro z T hz hT
  by_cases hr : log T/log z < H
  · rw [normalizedLower_two_step]
    exact (add_le_add le_rfl
      (hchild z T ((le_max_left _ _).trans ((le_max_left _ _).trans hz)) hT)).trans
      (hb z T ((le_max_right _ _).trans ((le_max_left _ _).trans hz)) hT hr)
  · exact (hexp z T ((le_max_right _ _).trans hz) hT).trans (htail _ (le_of_not_gt hr))

theorem bounded_refinement (N : ℕ) (H : ℝ) (φ : ℕ → ℝ → ℝ)
    (hzero : EventualProfile (φ 0))
    (hnonneg : ∀ n : ℕ, n < N → ∀ r : ℝ, 2 ≤ r → 0 ≤ φ n r)
    (htail : ∀ n : ℕ, n < N → ∀ r : ℝ, H ≤ r → 91*exp (-r) ≤ φ (n+1) r)
    (hstep : ∀ n : ℕ, n < N → ∃ B : ℝ, 2 ≤ B ∧ ∀ z T : ℝ, B ≤ z → z^2 ≤ T →
      log T/log z < H →
      forcing T z + operator (fun T z => φ n (log T/log z)) T z ≤ φ (n+1) (log T/log z)) :
    EventualProfile (φ N) := by
  have hind : ∀ n : ℕ, n ≤ N → EventualProfile (φ n) := by
    intro n
    induction n with
    | zero => exact fun _ => hzero
    | succ n ih =>
      intro hn
      have hn' : n < N := by omega
      exact refine_profile_below H (φ n) (φ (n+1)) (hnonneg n hn')
        (ih (by omega)) (htail n hn') (hstep n hn')
  exact hind N le_rfl

run_cmd do
  for decl in [``EventualProfile, ``profile_mono, ``initial_profile,
    ``operator_le_of_children, ``eventually_operator_le, ``refine_profile, ``finite_refinement,
    ``refine_profile_below, ``bounded_refinement] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FINITE ACTUAL STOPPING PROFILE REFINEMENT; ARITHMETIC TRANSFER INPUT EXPLICIT"
end SieveEventualProfile
end
