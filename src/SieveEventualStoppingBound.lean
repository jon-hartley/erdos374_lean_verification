import SieveStoppingDecay
import SieveStoppingSharpForcing
import SieveStoppingSharpOperator
import Mathlib.Analysis.SpecificLimits.Basic

/-! Eventual envelopes improve through the exact finite stopping recurrence.
Recursive cutoffs below the previous threshold have zero loss by finite
saturation. No uniform arithmetic error at small child cutoffs is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Filter
open scoped Topology

namespace SieveEventualStoppingBound
open SieveStoppingTwoStep SieveStoppingRecurrence

def EventualEnvelope (C : ℝ) : Prop :=
  ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
    normalizedLower T z ≤ C*exp (-(log T/log z))

theorem envelope_mono (C C' : ℝ) (h : EventualEnvelope C) (hCC : C ≤ C') :
    EventualEnvelope C' := by
  obtain ⟨Z, hZ, hb⟩ := h
  exact ⟨Z, hZ, fun z T hz hT => (hb z T hz hT).trans
    (mul_le_mul_of_nonneg_right hCC (exp_pos _).le)⟩

theorem global_envelope : EventualEnvelope SieveStoppingDecay.decayConstant :=
  ⟨2, le_rfl, fun z T hz hT => SieveStoppingDecay.normalizedLower_bound T z hz hT⟩

theorem small_child_saturated (T z Y : ℝ) (p q : ℕ)
    (hY : 2 ≤ Y) (hz : Y*SieveFiniteBase.saturationLevel Y ≤ z)
    (hz2 : 2 ≤ z) (hT : z^2 ≤ T)
    (hp : p ∈ SieveSmallWeights.pool z)
    (hq : q ∈ SieveSmallWeights.pool (p:ℝ)) (hqY : (q:ℝ) ≤ Y) :
    normalizedLower ((T/(p:ℝ))/(q:ℝ)) (q:ℝ) = 0 := by
  obtain ⟨hpp, hpz⟩ := (SieveSmallWeights.mem_pool z p).mp hp
  have hqp := ((SieveSmallWeights.mem_pool (p:ℝ) q).mp hq).1
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
  have hq0 : (0:ℝ) < q := by exact_mod_cast hqp.pos
  have hz0 : 0 < z := by linarith
  have hY0 : 0 < Y := by linarith
  have hTp : z < T/(p:ℝ) := by
    apply (lt_div_iff₀ hp0).mpr
    have hh := mul_lt_mul_of_pos_left hpz hz0
    nlinarith
  have hlevel : SieveFiniteBase.saturationLevel Y < (T/(p:ℝ))/(q:ℝ) := calc
    _ ≤ z/Y := (le_div_iff₀ hY0).mpr (by simpa only [mul_comm] using hz)
    _ ≤ z/(q:ℝ) := div_le_div_of_nonneg_left hz0.le hq0 hqY
    _ < _ := div_lt_div_of_pos_right hTp hq0
  have hprod : (((SieveSmallWeights.primes Y).prod^3 : ℕ):ℝ) <
      SieveFiniteBase.saturationLevel Y := by
    unfold SieveFiniteBase.saturationLevel
    exact (lt_add_one _).trans_le (le_max_right _ _)
  have hh := (SieveFiniteSaturation.uniform_finite_cutoff
    ((T/(p:ℝ))/(q:ℝ)) (q:ℝ) Y hqY (hprod.trans hlevel)).1
  simp only [normalizedLower, hh, zero_div]

/-- The cutoff threshold is enlarged before selecting either the parent
level or any recursive child. All bounded children are saturated exactly. -/
theorem improve_envelope (B F κ C : ℝ) (hB : 2 ≤ B) (hC : 0 ≤ C)
    (hforcing : ∀ T z : ℝ, B ≤ z → z^2 ≤ T →
      forcing T z ≤ F*exp (-(log T/log z)))
    (hoperator : ∀ T z : ℝ, B ≤ z → z^2 ≤ T →
      operator (fun T z => exp (-(log T/log z))) T z ≤
        κ*exp (-(log T/log z)))
    (henv : EventualEnvelope C) : EventualEnvelope (F+κ*C) := by
  obtain ⟨Y, hY, hb⟩ := henv
  let Z := max B (Y*SieveFiniteBase.saturationLevel Y)
  refine ⟨Z, hB.trans (le_max_left _ _), ?_⟩
  intro z T hz hT
  have hzB : B ≤ z := (le_max_left _ _).trans hz
  have hzY : Y*SieveFiniteBase.saturationLevel Y ≤ z := (le_max_right _ _).trans hz
  have hz2 : 2 ≤ z := hB.trans hzB
  have hchild : ∀ p ∈ SieveSmallWeights.pool z, ∀ q ∈ SieveSmallWeights.pool (p:ℝ),
      (q:ℝ)^3 < T/(p:ℝ) →
      normalizedLower ((T/(p:ℝ))/(q:ℝ)) (q:ℝ) ≤
        C*exp (-(log ((T/(p:ℝ))/(q:ℝ))/log (q:ℝ))) := by
    intro p hp q hq hg
    by_cases hqY : Y ≤ (q:ℝ)
    · exact hb (q:ℝ) ((T/(p:ℝ))/(q:ℝ)) hqY
        (SieveStoppingDecay.accepted_child_level T p q hq hg).2
    · rw [small_child_saturated T z Y p q hY hzY hz2 hT hp hq (le_of_not_ge hqY)]
      exact mul_nonneg hC (exp_pos _).le
  have ho := (SieveStoppingDecay.operator_bound_of_children T z C hchild).trans
    (mul_le_mul_of_nonneg_left (hoperator T z hzB hT) hC)
  rw [normalizedLower_two_step]
  calc
    _ ≤ F*exp (-(log T/log z))+C*(κ*exp (-(log T/log z))) :=
      add_le_add (hforcing T z hzB hT) ho
    _ = _ := by ring

theorem iterated_envelope (B : ℝ) (hB : 2 ≤ B)
    (hforcing : ∀ T z : ℝ, B ≤ z → z^2 ≤ T →
      forcing T z ≤ 15*exp (-(log T/log z)))
    (hoperator : ∀ T z : ℝ, B ≤ z → z^2 ≤ T →
      operator (fun T z => exp (-(log T/log z))) T z ≤
        (5/6)*exp (-(log T/log z))) (n : ℕ) :
    EventualEnvelope (90+SieveStoppingDecay.decayConstant*(5/6)^n) := by
  induction n with
  | zero =>
    apply envelope_mono _ _ global_envelope
    norm_num
  | succ n ih =>
    have hC : 0 ≤ 90+SieveStoppingDecay.decayConstant*(5/6)^n := by
      have hc := SieveStoppingDecay.decayConstant_pos.le
      positivity
    have hh := improve_envelope B 15 (5/6)
      (90+SieveStoppingDecay.decayConstant*(5/6)^n) hB hC hforcing hoperator ih
    convert hh using 1
    rw [pow_succ]
    ring

/-- Explicit sharper forcing and contraction estimates suffice for an
eventual coefficient 91, independently of the old global constant's size. -/
theorem eventually_ninety_one_of_sharp_bounds (B : ℝ) (hB : 2 ≤ B)
    (hforcing : ∀ T z : ℝ, B ≤ z → z^2 ≤ T →
      forcing T z ≤ 15*exp (-(log T/log z)))
    (hoperator : ∀ T z : ℝ, B ≤ z → z^2 ≤ T →
      operator (fun T z => exp (-(log T/log z))) T z ≤
        (5/6)*exp (-(log T/log z))) : EventualEnvelope 91 := by
  have hp : Tendsto (fun n : ℕ => (5/6:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hc := hp.const_mul SieveStoppingDecay.decayConstant
  simp only [mul_zero] at hc
  have he : ∀ᶠ n : ℕ in atTop, SieveStoppingDecay.decayConstant*(5/6)^n < 1 :=
    hc.eventually_lt_const (by norm_num)
  obtain ⟨n, hn⟩ := he.exists
  apply envelope_mono _ _ (iterated_envelope B hB hforcing hoperator n)
  linarith

/-- The actual normalized lower stopping loss eventually has coefficient 91,
uniformly over every level at least the square of its prime cutoff. -/
theorem eventually_ninety_one : EventualEnvelope 91 := by
  let B : ℝ := max 64 (exp (100000*PrimeEulerDimensionOne.errorConstant))
  have hB : 2 ≤ B := (by norm_num : (2:ℝ) ≤ 64).trans (le_max_left _ _)
  have hlarge : ∀ z : ℝ, B ≤ z →
      64 ≤ z ∧ 100000*PrimeEulerDimensionOne.errorConstant ≤ log z := by
    intro z hz
    refine ⟨(le_max_left _ _).trans hz, ?_⟩
    have he : exp (100000*PrimeEulerDimensionOne.errorConstant) ≤ z :=
      (le_max_right _ _).trans hz
    simpa only [log_exp] using log_le_log (exp_pos _) he
  apply eventually_ninety_one_of_sharp_bounds B hB
  · intro T z hz hT
    exact SieveStoppingSharpForcing.forcing_exponential T z
      (hlarge z hz).1 hT (hlarge z hz).2
  · intro T z hz hT
    exact SieveStoppingSharpOperator.operator_exponential_le T z
      (hlarge z hz).1 hT (hlarge z hz).2

run_cmd do
  for decl in [``EventualEnvelope, ``envelope_mono, ``global_envelope, ``small_child_saturated,
    ``improve_envelope, ``iterated_envelope, ``eventually_ninety_one_of_sharp_bounds,
    ``eventually_ninety_one] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EVENTUAL STOPPING ENVELOPE BOOTSTRAP; SMALL CHILDREN SATURATE EXACTLY"

end SieveEventualStoppingBound
end
