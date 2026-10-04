import SieveUpperProfileRecurrence
import SieveUpperProfileLinear
import SieveUpperProfileTail
import SieveProfileSupersolution

/-! Actual upper-selector bounds from a finite lower profile, its joined
tail, and its bootstrap allowance. A concrete postfixed certificate remains
an explicit input to the final generic theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real
open scoped BigOperators
namespace SieveUpperProfileBound
open SieveUpperProfileCumulative SieveUpperProfileLinear SieveUpperProfileRecurrence

def profile {ι : Type*} (S : Finset ι) (d c : ι → ℝ) (r : ℝ) : ℝ :=
  staircase S d c r+SieveProfileExponentialTail.tail r

theorem profile_nonneg {ι : Type*} (S : Finset ι) (d c : ι → ℝ)
    (hd : ∀ i ∈ S, 0 ≤ d i) (r : ℝ) : 0 ≤ profile S d c r :=
  add_nonneg (staircase_nonneg S d c hd r) (SieveProfileExponentialTail.tail_nonneg r)

theorem profile_tail {ι : Type*} (S : Finset ι) (d c : ι → ℝ)
    (hd : ∀ i ∈ S, 0 ≤ d i) (r : ℝ) (hr : 20 ≤ r) :
    91*exp (-r) ≤ profile S d c r := by
  unfold profile SieveProfileExponentialTail.tail
  simp only [hr, ite_true]
  linarith [staircase_nonneg S d c hd r]

/-- The tail and the bootstrap error are actual one-prime selector-mass
allowances. They are not silently identified with continuum area integrals. -/
theorem eventually_augmented_sum {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (d c : ι → ℝ)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hc : ∀ i ∈ S, 2 ≤ c i)
    (ε : ℝ) (hε : 0 ≤ ε) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      onePrime (fun T z => profile S d c (log T/log z)+ε*exp (-(log T/log z))) T z ≤
        area S d c/3+1/10000+ε+δ := by
  obtain ⟨A, hA, ha⟩ := eventually_staircase S d c hd hc δ hδ
  obtain ⟨B, _hB, hb⟩ := SieveUpperProfileTail.eventually_both
  refine ⟨max A B, hA.trans (le_max_left _ _), ?_⟩
  intro z T hz hT
  have hs := ha z T ((le_max_left _ _).trans hz) hT
  obtain ⟨ht, he⟩ := hb z T ((le_max_right _ _).trans hz) hT
  have he' := mul_le_mul_of_nonneg_left he hε
  dsimp only [profile]
  rw [onePrime_add, onePrime_add, onePrime_const_mul]
  linarith

theorem eventually_upper_of_profile {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (d c : ι → ℝ)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hc : ∀ i ∈ S, 2 ≤ c i)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hprofile : SieveEventualProfile.EventualProfile
      (fun r => profile S d c r+ε*exp (-r)))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      SieveFullCutoffTransfer.fullUpper T z ≤
        (1+area S d c/3+1/10000+ε+δ)*SieveStoppingExpansion.primeEuler z := by
  have hn : ∀ r : ℝ, 2 ≤ r → 0 ≤ profile S d c r+ε*exp (-r) := by
    intro r _hr
    exact add_nonneg (profile_nonneg S d c hd r) (mul_nonneg hε (exp_pos _).le)
  obtain ⟨A, hA, ha⟩ := eventually_upper_le _ hn hprofile
  obtain ⟨B, _hB, hb⟩ := eventually_augmented_sum S d c hd hc ε hε δ hδ
  refine ⟨max A B, hA.trans (le_max_left _ _), ?_⟩
  intro z T hz hT
  have hu := (ha z T ((le_max_left _ _).trans hz) hT).trans
    (hb z T ((le_max_right _ _).trans hz) hT)
  have hh := fullUpper_le_of_normalized T z _ hu
  convert hh using 1
  ring

/-- A genuine actual postfixed estimate supplies the lower-profile input
through the checked finite bootstrap. The concrete postfixed input is not
proved or assumed implicitly by this generic assembly theorem. -/
theorem eventually_upper_of_postfixed {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (d c : ι → ℝ)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hc : ∀ i ∈ S, 2 ≤ c i)
    (hpost : SieveProfileSupersolution.Postfixed (profile S d c))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      SieveFullCutoffTransfer.fullUpper T z ≤
        (1+area S d c/3+1/5000+δ)*SieveStoppingExpansion.primeEuler z := by
  have hp := SieveProfileSupersolution.bootstrap (profile S d c)
    (fun r _hr => profile_nonneg S d c hd r) (profile_tail S d c hd)
    hpost (1/10000:ℝ) (by norm_num)
  obtain ⟨Z, hZ, hb⟩ := eventually_upper_of_profile S d c hd hc (1/10000)
    (by norm_num) hp δ hδ
  refine ⟨Z, hZ, ?_⟩
  intro z T hz hT
  convert hb z T hz hT using 1
  ring

run_cmd do
  for decl in [``profile_nonneg, ``profile_tail, ``eventually_augmented_sum,
      ``eventually_upper_of_profile, ``eventually_upper_of_postfixed] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL UPPER SELECTOR FROM LOWER PROFILE; POSTFIXED INPUT EXPLICIT"
end SieveUpperProfileBound
end
