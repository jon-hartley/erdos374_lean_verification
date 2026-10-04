import SieveEventualProfile
import SieveProfileOperatorLinear
import SieveStoppingSharpOperator

/-! Generic bootstrap from an actual postfixed stopping profile. The
postfixed inequality is an explicit input; this module does not certify
any new numerical profile. Small recursive cutoffs are handled by the
previous exact-saturation refinement theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Filter
open scoped Topology
namespace SieveProfileSupersolution
open SieveStoppingTwoStep SieveEventualProfile

def Postfixed (φ : ℝ → ℝ) : Prop :=
  ∃ B : ℝ, 2 ≤ B ∧ ∀ z T : ℝ, B ≤ z → z^2 ≤ T →
    log T/log z < 20 →
    forcing T z+operator (fun T z => φ (log T/log z)) T z ≤ φ (log T/log z)

def excess (n : ℕ) : ℝ := 91*(5/6)^n

theorem excess_nonneg (n : ℕ) : 0 ≤ excess n := by
  unfold excess
  positivity

theorem excess_succ (n : ℕ) : excess (n+1) = excess n*(5/6) := by
  simp only [excess, pow_succ, mul_assoc]

theorem eventually_exponential_contraction :
    ∃ B : ℝ, 2 ≤ B ∧ ∀ z T : ℝ, B ≤ z → z^2 ≤ T →
      operator (fun T z => exp (-(log T/log z))) T z ≤
        (5/6)*exp (-(log T/log z)) := by
  let B : ℝ := max 64 (exp (100000*PrimeEulerDimensionOne.errorConstant))
  refine ⟨B, (by norm_num : (2:ℝ) ≤ 64).trans (le_max_left _ _), ?_⟩
  intro z T hz hT
  have hz64 : 64 ≤ z := (le_max_left _ _).trans hz
  have hlog : 100000*PrimeEulerDimensionOne.errorConstant ≤ log z := by
    have he : exp (100000*PrimeEulerDimensionOne.errorConstant) ≤ z :=
      (le_max_right _ _).trans hz
    simpa only [log_exp] using log_le_log (exp_pos _) he
  exact SieveStoppingSharpOperator.operator_exponential_le T z hz64 hT hlog

/-- One bounded refinement contracts only the excess above the postfixed
profile. Its threshold precedes both the later cutoff and level. -/
theorem contract_excess (φ : ℝ → ℝ)
    (hφ0 : ∀ r : ℝ, 2 ≤ r → 0 ≤ φ r)
    (htail : ∀ r : ℝ, 20 ≤ r → 91*exp (-r) ≤ φ r)
    (hpost : Postfixed φ) (C : ℝ) (hC : 0 ≤ C)
    (henv : EventualProfile (fun r => φ r+C*exp (-r))) :
    EventualProfile (fun r => φ r+(C*(5/6))*exp (-r)) := by
  apply refine_profile_below 20 (fun r => φ r+C*exp (-r))
    (fun r => φ r+(C*(5/6))*exp (-r))
  · intro r hr
    exact add_nonneg (hφ0 r hr) (mul_nonneg hC (exp_pos _).le)
  · exact henv
  · intro r hr
    exact (htail r hr).trans (le_add_of_nonneg_right (by positivity))
  · obtain ⟨B, hB, hb⟩ := hpost
    obtain ⟨E, _hE, he⟩ := eventually_exponential_contraction
    refine ⟨max B E, hB.trans (le_max_left _ _), ?_⟩
    intro z T hz hT hr
    have hp := hb z T ((le_max_left _ _).trans hz) hT hr
    have hc := mul_le_mul_of_nonneg_left
      (he z T ((le_max_right _ _).trans hz) hT) hC
    rw [SieveProfileOperatorLinear.operator_add,
      SieveProfileOperatorLinear.operator_const_mul]
    calc
      _ = (forcing T z+operator (fun T z => φ (log T/log z)) T z)+
          C*operator (fun T z => exp (-(log T/log z))) T z := by ring
      _ ≤ φ (log T/log z)+C*((5/6)*exp (-(log T/log z))) := add_le_add hp hc
      _ = _ := by ring

/-- Every fixed finite number of refinements is valid for the actual
stopping loss. There is no infinite intersection of cutoff thresholds. -/
theorem finite_bootstrap (φ : ℝ → ℝ)
    (hφ0 : ∀ r : ℝ, 2 ≤ r → 0 ≤ φ r)
    (htail : ∀ r : ℝ, 20 ≤ r → 91*exp (-r) ≤ φ r)
    (hpost : Postfixed φ) (n : ℕ) :
    EventualProfile (fun r => φ r+excess n*exp (-r)) := by
  induction n with
  | zero =>
    apply profile_mono _ _ initial_profile
    intro r hr
    simp only [excess, pow_zero, mul_one]
    linarith [hφ0 r hr]
  | succ n ih =>
    simpa only [excess_succ] using
      contract_excess φ hφ0 htail hpost (excess n) (excess_nonneg n) ih

/-- An actual postfixed profile is approached with an arbitrarily small
exponential allowance. The postfixed arithmetic estimate remains explicit. -/
theorem bootstrap (φ : ℝ → ℝ)
    (hφ0 : ∀ r : ℝ, 2 ≤ r → 0 ≤ φ r)
    (htail : ∀ r : ℝ, 20 ≤ r → 91*exp (-r) ≤ φ r)
    (hpost : Postfixed φ) (ε : ℝ) (hε : 0 < ε) :
    EventualProfile (fun r => φ r+ε*exp (-r)) := by
  have hp : Tendsto (fun n : ℕ => (5/6:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hc := hp.const_mul 91
  simp only [mul_zero] at hc
  have he : ∀ᶠ n : ℕ in atTop, excess n < ε := hc.eventually_lt_const hε
  obtain ⟨n, hn⟩ := he.exists
  apply profile_mono _ _ (finite_bootstrap φ hφ0 htail hpost n)
  intro r _hr
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hn.le (exp_pos _).le)

run_cmd do
  for decl in [``Postfixed, ``excess_nonneg, ``excess_succ,
      ``eventually_exponential_contraction, ``contract_excess, ``finite_bootstrap,
      ``bootstrap] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "GENERIC ACTUAL POSTFIXED PROFILE BOOTSTRAP; POSTFIXED INPUT EXPLICIT"

end SieveProfileSupersolution
end
