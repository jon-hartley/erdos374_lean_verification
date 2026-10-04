import SieveUpperProfileCumulative
import SieveEventualProfile
import SieveFullCutoffTransfer

/-! Exact upper-selector recurrence and uniform transfer from an eventual
lower-loss profile. Bounded child cutoffs have zero loss by finite saturation. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real
open scoped BigOperators
namespace SieveUpperProfileRecurrence
open SieveStoppingExpansion SieveStoppingRecurrence SieveStoppingTwoStep
open SieveUpperProfileCumulative

theorem upper_eq_onePrime (T z : ℝ) (hT : z^3 ≤ T) :
    upperLoss T z/primeEuler z = onePrime normalizedLower T z := by
  rw [upperLoss_first_prime, Finset.sum_div, onePrime]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [all_gates T z hT p hp, ite_true]
  unfold normalizedLower PrimeEulerMass.weight
  have hVp := (SieveEulerRatio.euler_pos (p:ℝ)).ne'
  field_simp

theorem child_level (T z : ℝ) (hT : z^3 ≤ T) (p : ℕ)
    (hp : p ∈ SieveSmallWeights.pool z) : (p:ℝ)^2 ≤ T/(p:ℝ) := by
  have hpp := ((SieveSmallWeights.mem_pool z p).mp hp).1
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
  apply (le_div_iff₀ hp0).mpr
  simpa only [pow_succ] using (all_gates T z hT p hp).le

theorem small_child_saturated (T z Y : ℝ) (p : ℕ) (hz : 2 ≤ z)
    (hsat : SieveFiniteBase.saturationLevel Y ≤ z) (hT : z^3 ≤ T)
    (hp : p ∈ SieveSmallWeights.pool z) (hpY : (p:ℝ) ≤ Y) :
    normalizedLower (T/(p:ℝ)) (p:ℝ) = 0 := by
  obtain ⟨hpp, hpz⟩ := (SieveSmallWeights.mem_pool z p).mp hp
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
  have hz0 : 0 < z := by linarith
  have hchild : z^2 < T/(p:ℝ) := by
    apply (lt_div_iff₀ hp0).mpr
    have hh := mul_lt_mul_of_pos_left hpz (sq_pos_of_pos hz0)
    nlinarith
  have hprod : (((SieveSmallWeights.primes Y).prod^3 : ℕ):ℝ) <
      SieveFiniteBase.saturationLevel Y :=
    (lt_add_one _).trans_le (le_max_right _ _)
  have hlevel : (((SieveSmallWeights.primes Y).prod^3 : ℕ):ℝ) < T/(p:ℝ) := by
    nlinarith
  have hh := (SieveFiniteSaturation.uniform_finite_cutoff (T/(p:ℝ)) (p:ℝ) Y hpY hlevel).1
  simp only [normalizedLower, hh, zero_div]

/-- One threshold handles every first-prime child: large children use the
given actual lower profile and small children are exactly saturated. -/
theorem eventually_upper_le (φ : ℝ → ℝ)
    (hφ0 : ∀ r : ℝ, 2 ≤ r → 0 ≤ φ r)
    (hφ : SieveEventualProfile.EventualProfile φ) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      upperLoss T z/primeEuler z ≤ onePrime (fun T z => φ (log T/log z)) T z := by
  obtain ⟨Y, hY, hb⟩ := hφ
  let Z := max Y (SieveFiniteBase.saturationLevel Y)
  refine ⟨Z, hY.trans (le_max_left _ _), ?_⟩
  intro z T hz hT
  have hz2 : 2 ≤ z := hY.trans ((le_max_left _ _).trans hz)
  rw [upper_eq_onePrime T z hT, onePrime, onePrime]
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (weight_nonneg p z)
  have hp2 : (2:ℝ) ≤ p := by
    exact_mod_cast ((SieveSmallWeights.mem_pool z p).mp hp).1.two_le
  have hlevel := child_level T z hT p hp
  by_cases hpY : Y ≤ (p:ℝ)
  · exact hb (p:ℝ) (T/(p:ℝ)) hpY hlevel
  · rw [small_child_saturated T z Y p hz2 ((le_max_right _ _).trans hz)
      hT hp (le_of_not_ge hpY)]
    exact hφ0 _ (SieveStoppingArithmeticContraction.parameter_ge_two _ _ hp2 hlevel)

theorem fullUpper_eq_euler_add_loss (T z : ℝ) :
    SieveFullCutoffTransfer.fullUpper T z = primeEuler z+upperLoss T z := by
  unfold SieveFullCutoffTransfer.fullUpper upperLoss SievePrefixLoss.upper primeEuler
  ring

theorem fullUpper_le_of_normalized (T z C : ℝ)
    (h : upperLoss T z/primeEuler z ≤ C) :
    SieveFullCutoffTransfer.fullUpper T z ≤ (1+C)*primeEuler z := by
  have hh := (div_le_iff₀ (SieveEulerRatio.euler_pos z)).mp h
  rw [fullUpper_eq_euler_add_loss]
  nlinarith

run_cmd do
  for decl in [``upper_eq_onePrime, ``child_level, ``small_child_saturated,
      ``eventually_upper_le, ``fullUpper_eq_euler_add_loss, ``fullUpper_le_of_normalized] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL UPPER SELECTOR TRANSFER; BOUNDED FIRST-PRIME CHILDREN SATURATE"
end SieveUpperProfileRecurrence
end
