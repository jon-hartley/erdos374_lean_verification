import PrimeReciprocalBoundsRefined
import SieveBoxMassRefined

/-! Stronger unconditional actual box masses, using the Chebyshev constant two.
The refined profile factor costs only s^(-17/4), while each band costs O(s^9). -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
open Filter SieveGeometricGrid SieveBoxMass

namespace SieveBoxMassTwo

theorem actual_prime_mass_bounds_two :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ (D s z : ℝ), 1 < D → 0 < s → s ≤ 1 →
      W ≤ D^(s^2) → z ≤ D →
      (∀ i : ℕ, bandMass D s z i ≤
        2 * Real.log (ratio s) + 3 / Real.log (D^(s^2))) ∧
      primeMass D s z ≤
        2 * Real.log (1 / s^2) + 3 / Real.log (D^(s^2)) := by
  obtain ⟨W₁, hW₁, hinterval⟩ :=
    PrimeReciprocalBoundsRefined.eventual_reciprocal_interval_bound_two
  obtain ⟨W₂, hW₂, hband⟩ :=
    PrimeReciprocalBoundsRefined.eventual_reciprocal_geometric_bound_two
  refine ⟨max W₁ W₂, hW₁.trans (le_max_left _ _), ?_⟩
  intro D s z hD hs hs1 hW hz
  have hs2 : 0 < s^2 := sq_pos_of_pos hs
  have hD0 : 0 < D := by linarith
  have huD : D^(s^2) ≤ D := by
    have hexp : s^2 ≤ 1 := by nlinarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hD.le hexp
  constructor
  · intro i
    apply hband (D^(s^2)) (scale D s i) (ratio s)
      (SieveBoxGrouping.primeBand D s z i) ((le_max_right _ _).trans hW)
    · simpa only [scale_zero] using
        (scale_strictMono D s hD hs).monotone (Nat.zero_le i)
    · exact (one_lt_ratio s hs).le
    · intro p hp
      obtain ⟨hpp, _, hpbox⟩ := (SieveBoxGrouping.mem_primeBand D s z i p).mp hp
      refine ⟨hpp, hpbox.1, ?_⟩
      simpa only [scale_succ D s hD0.le] using hpbox.2.le
  · have hi := hinterval (D^(s^2)) D (SieveBoxedFamily.pool D s z)
      ((le_max_left _ _).trans hW) huD (by
        intro p hp
        obtain ⟨hpp, hpz, hpu⟩ := (SieveBoxedFamily.mem_pool D s z p).mp hp
        exact ⟨hpp, hpu, hpz.le.trans hz⟩)
    have hratio : Real.log D / Real.log (D^(s^2)) = 1 / s^2 := by
      rw [Real.log_rpow hD0]
      have hlog : Real.log D ≠ 0 := ne_of_gt (Real.log_pos hD)
      field_simp
    simpa only [primeMass, hratio] using hi

def growth (s : ℝ) : ℝ := Real.exp ((17 : ℝ)/16) * (1/s^2)^((17 : ℝ)/8)

/-- One threshold, independent of the upper prime cutoff, controls every actual
band and both complete unsigned tuple families. -/
theorem eventually_total_mass_sharp (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (hsmall : 2 * Real.log (ratio s) < 1/17) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ, z ≤ D →
      (∀ i : ℕ, bandMass D s z i ≤ 1/17) ∧
      (∀ i : ℕ, bandMass D s z i ≤ 3*s^9) ∧
      primeMass D s z ≤ 2 * Real.log (1/s^2) + 1 ∧
      mass true D s z + mass false D s z ≤ growth s := by
  obtain ⟨W, _, hW⟩ := actual_prime_mass_bounds_two
  let δ : ℝ := 1/17 - 2 * Real.log (ratio s)
  let e : ℝ := min δ (min (s^9) 1)
  have hδ : 0 < δ := sub_pos.mpr hsmall
  have he : 0 < e := lt_min hδ (lt_min (by positivity) (by norm_num))
  have ht : Tendsto (fun D : ℝ => D^(s^2)) atTop atTop :=
    tendsto_rpow_atTop (sq_pos_of_pos hs)
  have hev : ∀ᶠ D : ℝ in atTop,
      2 ≤ D ∧ W ≤ D^(s^2) ∧ 3/e ≤ Real.log (D^(s^2)) := by
    filter_upwards [eventually_ge_atTop 2, ht.eventually_ge_atTop W,
      (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop (3/e)] with D hD hu hl
    exact ⟨hD, hu, hl⟩
  obtain ⟨D₁, hD₁⟩ := eventually_atTop.1 hev
  refine ⟨max 2 D₁, by have := le_max_left (2 : ℝ) D₁; linarith, ?_⟩
  intro D hD z hz
  obtain ⟨hD2, hu, hl⟩ := hD₁ D ((le_max_right _ _).trans hD)
  have hD1 : 1 < D := by linarith
  have hlog : 0 < Real.log (D^(s^2)) :=
    Real.log_pos (Real.one_lt_rpow hD1 (sq_pos_of_pos hs))
  have herr : 3 / Real.log (D^(s^2)) ≤ e := by
    apply (div_le_iff₀ hlog).mpr
    have hh := (div_le_iff₀ he).mp hl
    nlinarith
  have heδ : e ≤ δ := min_le_left _ _
  have he9 : e ≤ s^9 := (min_le_right _ _).trans (min_le_left _ _)
  have he1 : e ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hlogq : Real.log (ratio s) ≤ s^9 := by
    have h := Real.log_le_sub_one_of_pos
      (show 0 < ratio s from zero_lt_one.trans (one_lt_ratio s hs))
    simpa only [ratio, add_sub_cancel_left] using h
  obtain ⟨hb, hp⟩ := hW D s z hD1 hs hs1 hu hz
  have hcap : ∀ i : ℕ, bandMass D s z i ≤ 1/17 := by
    intro i
    have hi := hb i
    dsimp only [δ] at heδ
    linarith
  have hprime : primeMass D s z ≤ 2 * Real.log (1/s^2) + 1 := by linarith
  refine ⟨hcap, fun i => ?_, hprime, ?_⟩
  · have hi := hb i
    linarith
  · calc
      _ ≤ Real.exp ((17/16 : ℝ) * primeMass D s z) :=
        total_mass_le_exp_sharp_of_band_bound D s z hD1 hs hz (fun i _ => hcap i)
      _ ≤ Real.exp ((17/16 : ℝ) * (2 * Real.log (1/s^2) + 1)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hprime (by norm_num)
      _ = growth s := by
        rw [show (17/16 : ℝ) * (2 * Real.log (1/s^2) + 1) =
          (17/16 : ℝ) + Real.log (1/s^2) * (17/8 : ℝ) by ring,
          Real.exp_add, Real.exp_mul, Real.exp_log (by positivity)]
        rfl

theorem small_parameter_total_mass_sharp (s : ℝ) (hs : 0 < s) (hsHalf : s ≤ 1/2) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ, z ≤ D →
      (∀ i : ℕ, bandMass D s z i ≤ 1/17) ∧
      (∀ i : ℕ, bandMass D s z i ≤ 3*s^9) ∧
      primeMass D s z ≤ 2 * Real.log (1/s^2) + 1 ∧
      mass true D s z + mass false D s z ≤ growth s := by
  apply eventually_total_mass_sharp s hs (by linarith)
  have hp : s^9 ≤ (1/2 : ℝ)^9 := by gcongr
  have hl := Real.log_le_sub_one_of_pos
    (show 0 < ratio s from zero_lt_one.trans (one_lt_ratio s hs))
  dsimp only [ratio] at hl ⊢
  norm_num at hp
  linarith

/-- The complete quantitative input for normalized collision estimates.
All conditions are proved for one threshold before `D`, `z`, and every band. -/
theorem small_parameter_bounds_two (s : ℝ) (hs : 0 < s) (hsHalf : s ≤ 1/2) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ, z ≤ D →
      17 ≤ D^(s^2) ∧
      (∀ i : ℕ, bandMass D s z i ≤ 1/17) ∧
      (∀ i : ℕ, bandMass D s z i ≤ 3*s^9) ∧
      primeMass D s z ≤ 2 * Real.log (1/s^2) + 1 ∧
      mass true D s z + mass false D s z ≤ growth s := by
  obtain ⟨D₁, hD₁, hmass⟩ := small_parameter_total_mass_sharp s hs hsHalf
  have he := (tendsto_rpow_atTop (sq_pos_of_pos hs)).eventually_ge_atTop (17 : ℝ)
  obtain ⟨D₂, hD₂⟩ := eventually_atTop.1 he
  refine ⟨max D₁ D₂, hD₁.trans_le (le_max_left _ _), fun D hD z hz => ?_⟩
  exact ⟨hD₂ D ((le_max_right _ _).trans hD),
    hmass D ((le_max_left _ _).trans hD) z hz⟩

#print axioms small_parameter_total_mass_sharp
#print axioms small_parameter_bounds_two
run_cmd do
  for decl in [``actual_prime_mass_bounds_two, ``eventually_total_mass_sharp,
    ``small_parameter_total_mass_sharp, ``small_parameter_bounds_two] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end SieveBoxMassTwo
end
