import Item1ShrinkingCircleGrowth
import Item1AutomaticZetaDetector
import Item1ZetaDiskGeometry

/-! Uniform actual zeta exclusion from one modulus estimate.
The original-circle growth bounds and the real-axis pole bound are constructed
inside this chain. The modulus estimate itself remains an explicit premise.
All thresholds are fixed before the arbitrary height and real part. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Filter Set Complex
namespace Item1GrowthToZeroFree
open Item1ZeroFreeScaleClock Item1DetectorPoleAnchor
open Item1ShrinkingCircleGrowth Item1AutomaticZetaDetector Item1ZetaDiskGeometry

/-- Only the genuinely difficult left-of-one part of the growth theorem.
The wider upper range through sigma=2 is supplied from the retained source. -/
def LeftLogarithmicZetaGrowth (A : ℕ) (C Tg : ℝ) : Prop :=
  ∀ u v : ℝ, Tg≤v → 1-1/(Real.log v)^(2/3:ℝ)≤u → u≤1 →
    ‖riemannZeta ((u:ℂ)+(v:ℂ)*Complex.I)‖≤C*(Real.log v)^A

theorem extend_left_growth (A : ℕ) (C Tg : ℝ) (hC : 1≤C)
    (hg : LeftLogarithmicZetaGrowth A C Tg) :
    ∃ A' : ℕ, ∃ C' Tg' : ℝ, 1≤C' ∧
      LogarithmicZetaGrowth A' C' Tg' := by
  obtain ⟨a,ha,D,hD,hright⟩ := ZetaUpperBnd
  let A' := max A 1
  let C' := C+D+1
  let T' := max (max Tg 4) (Real.exp 1)
  refine ⟨A',C',T',by dsimp [C']; linarith,?_⟩
  intro u v hv hulo hu2
  have hvg : Tg≤v := (le_max_left Tg 4).trans ((le_max_left _ _).trans hv)
  have hv4 : 4≤v := (le_max_right Tg 4).trans ((le_max_left _ _).trans hv)
  have hvp : 0<v := by linarith
  have hvlog : 1≤Real.log v :=
    (Real.le_log_iff_exp_le hvp).mpr ((le_max_right _ _).trans hv)
  have hC' : C≤C' := by dsimp [C']; linarith
  have hD' : D≤C' := by dsimp [C']; linarith
  by_cases hu1 : u≤1
  · have hh := hg u v hvg hulo hu1
    apply hh.trans
    apply mul_le_mul hC'
      (pow_le_pow_right₀ hvlog (show A≤A' from le_max_left _ _))
      (pow_nonneg (by linarith) A) (by dsimp [C']; positivity)
  · have hlogp : 0<Real.log v := by linarith
    have hs : 1-a/Real.log |v|≤u := by
      rw [abs_of_pos hvp]
      have hd := div_nonneg ha.1.le hlogp.le
      linarith
    have hh := hright u v (by rw [abs_of_pos hvp]; linarith) ⟨hs,hu2⟩
    rw [abs_of_pos hvp] at hh
    apply hh.trans
    have hp : Real.log v≤(Real.log v)^A' := by
      simpa only [pow_one] using pow_le_pow_right₀ hvlog (le_max_right A 1)
    exact mul_le_mul hD' hp hlogp.le (by dsimp [C']; positivity)

/-- No disk-growth, pole, anchor, zero-list, or nonvanishing premise appears
here. The stated upper modulus estimate is the one unproved analytic argument. -/
theorem eventually_zero_free_of_growth (A : ℕ) (C Tg : ℝ)
    (hC : 1≤C) (hg : LogarithmicZetaGrowth A C Tg) :
    ∀ᶠ t : ℝ in atTop, ∀ beta : ℝ,
      1-(1/20)/(Real.log t)^(3/4:ℝ)≤beta →
      riemannZeta ((beta:ℂ)+(t:ℂ)*Complex.I)≠0 := by
  obtain ⟨c,hc,ha⟩ := exists_moving_anchor
  obtain ⟨eps,heps,hpole⟩ := exists_pole_guard
  filter_upwards [eventually_scalar_guards A c C eps hc (by linarith) heps,
    eventually_ge_atTop (9:ℝ),eventually_ge_atTop (2*Real.exp 1),
    eventually_ge_atTop (2*Tg)] with t hs ht htE htG
  let x := clock t
  have hxp : 0<x := by dsimp [x]; linarith [hs.1]
  have htid := clock_identities t (by linarith)
  have hL : x^12=Real.log t := htid.1
  obtain ⟨hh,hh1,hR,hR1,hr,hM⟩ := scale_guards A x hs.1
  have hgt : radius x<t := by linarith
  have hpol := hpole (step x) hh hs.2.1
  have hg1 := disk_growth_of_modulus A c C Tg x t t hc (by linarith) hg
    hs.1 ht htE htG hL le_rfl (by linarith) hs.2.2.1 ha
  have hg2 := disk_growth_of_modulus A c C Tg x t (2*t) hc (by linarith) hg
    hs.1 ht htE htG hL (by linarith) le_rfl hs.2.2.1 ha
  have he : 1-step x/20=1-(1/20)/(Real.log t)^(3/4:ℝ) := by
    unfold step
    rw [htid.2.2]
    ring
  intro beta hb
  have hb' : 1-step x/20≤beta := by rwa [he]
  have hzero := local_zeta_exclusion_all_right (step x) (radius x)
    (growth A x) t beta hh hR hM hgt hr hs.2.2.2 hpol hg1 hg2 hb'
  simpa only [Item1AutomaticZetaDetector.center] using hzero

/-- The parent's exact closed-right strip contract, with b fixed at 1/20. -/
theorem bare_zero_free_of_growth (A : ℕ) (C Tg : ℝ) (hC : 1≤C)
    (hg : LogarithmicZetaGrowth A C Tg) :
    ∃ T : ℝ, 4≤T ∧ BarePositiveZeroFree (1/20) T := by
  obtain ⟨T,hT⟩ := eventually_atTop.1 (eventually_zero_free_of_growth A C Tg hC hg)
  refine ⟨max T 4,le_max_right _ _,?_⟩
  intro sigma t ht hs _hs4
  exact hT t ((le_max_left T 4).trans ht) sigma hs

theorem bare_zero_free_of_left_growth (A : ℕ) (C Tg : ℝ) (hC : 1≤C)
    (hg : LeftLogarithmicZetaGrowth A C Tg) :
    ∃ T : ℝ, 4≤T ∧ BarePositiveZeroFree (1/20) T := by
  obtain ⟨A',C',Tg',hC',hg'⟩ := extend_left_growth A C Tg hC hg
  exact bare_zero_free_of_growth A' C' Tg' hC' hg'

end Item1GrowthToZeroFree

run_cmd do
  for target in [``Item1GrowthToZeroFree.extend_left_growth,
    ``Item1GrowthToZeroFree.eventually_zero_free_of_growth,
    ``Item1GrowthToZeroFree.bare_zero_free_of_growth,
    ``Item1GrowthToZeroFree.bare_zero_free_of_left_growth] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1GrowthToZeroFree.bare_zero_free_of_left_growth
