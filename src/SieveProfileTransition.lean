import SieveForcingProfileRectangles
import SieveProfileOperatorLinear
import SieveProfileExponentialTail

/-! One actual transition of a finite positive staircase with an exponential
tail. Every coefficient is a literal rectangle; one threshold precedes all
parent levels and cutoffs. No numeric certificate interpretation is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real
open scoped BigOperators
namespace SieveProfileTransition
open SieveStoppingTwoStep SieveProfileOperatorGrid SieveProfileOperatorCumulative

def staircase {ι : Type*} (S : Finset ι) (d c : ι → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ S, d i*(if r ≤ c i then 1 else 0)

def profile {ι : Type*} (S : Finset ι) (d c : ι → ℝ) (r : ℝ) : ℝ :=
  staircase S d c r + SieveProfileExponentialTail.tail r

def rowBound {ι : Type*} (S : Finset ι) (d c : ι → ℝ) (r h : ℝ)
    (NF : ℕ) (N : ι → ℕ) : ℝ :=
  SieveForcingProfileRectangles.rectangles r h NF+
    (∑ i ∈ S, d i*(h*∑ k ∈ Finset.range (N i), shape (c i) (r*edge h k-1)))+
    1/10000

theorem staircase_nonneg {ι : Type*} (S : Finset ι) (d c : ι → ℝ)
    (hd : ∀ i ∈ S, 0 ≤ d i) (r : ℝ) : 0 ≤ staircase S d c r := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hd i hi) (by split_ifs <;> norm_num)

theorem profile_nonneg {ι : Type*} (S : Finset ι) (d c : ι → ℝ)
    (hd : ∀ i ∈ S, 0 ≤ d i) (r : ℝ) : 0 ≤ profile S d c r :=
  add_nonneg (staircase_nonneg S d c hd r) (SieveProfileExponentialTail.tail_nonneg r)

theorem profile_tail_lower {ι : Type*} (S : Finset ι) (d c : ι → ℝ)
    (hd : ∀ i ∈ S, 0 ≤ d i) (r : ℝ) (hr : 20 ≤ r) :
    91*exp (-r) ≤ profile S d c r := by
  unfold profile SieveProfileExponentialTail.tail
  simp only [hr, ite_true]
  linarith [staircase_nonneg S d c hd r]

theorem eventually_tail :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
      operator (fun T z => SieveProfileExponentialTail.tail (log T/log z)) T z ≤
        (1/10000:ℝ) := by
  let B := max 400 (100000*PrimeEulerDimensionOne.errorConstant)
  refine ⟨max 2 (exp B), le_max_left _ _, ?_⟩
  intro z T hz hT
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hz
  have hlz : 0 < log z := log_pos (by linarith)
  have hlog : B ≤ log z := by
    have hh := log_le_log (exp_pos B) ((le_max_right _ _).trans hz)
    simpa only [log_exp] using hh
  have h400 : 400 ≤ log z := (le_max_left _ _).trans hlog
  have he : PrimeEulerDimensionOne.errorConstant/log z ≤ 1/100000 := by
    apply (div_le_iff₀ hlz).mpr
    have hh := (le_max_right 400 (100000*PrimeEulerDimensionOne.errorConstant)).trans hlog
    linarith
  exact SieveProfileExponentialTail.operator_tail_bound T z hz2 hT h400 he

theorem operator_profile_eq {ι : Type*} (S : Finset ι) (d c : ι → ℝ) (T z : ℝ) :
    operator (fun T z => profile S d c (log T/log z)) T z =
      operator (fun T z => staircase S d c (log T/log z)) T z+
      operator (fun T z => SieveProfileExponentialTail.tail (log T/log z)) T z := by
  exact SieveProfileOperatorLinear.operator_add _ _ T z

/-- For every positive error, a common threshold bounds the complete actual
forcing-plus-operator expression by its finite row budget and that error. -/
theorem eventually_transition {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (d c : ι → ℝ) (r h : ℝ) (NF : ℕ) (N : ι → ℕ)
    (hr : 2 ≤ r) (hh : 0 ≤ h)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hc : ∀ i ∈ S, 2 ≤ c i)
    (hforcingCover : 4/r ≤ 1+(NF:ℝ)*h)
    (hforcingLeft : ∀ k < NF, 1+(k:ℝ)*h ≤ 4/r)
    (hcover : ∀ i ∈ S, c i+2 ≤ r*edge h (N i))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T → r ≤ log T/log z →
      forcing T z+operator (fun T z => profile S d c (log T/log z)) T z ≤
        rowBound S d c r h NF N+δ := by
  have hdHalf : 0 < δ/2 := by linarith
  obtain ⟨ZF, hZF, hF⟩ := SieveForcingProfileRectangles.eventually_forcing_rectangles
    r h NF hr hh hforcingCover hforcingLeft (δ/2) hdHalf
  obtain ⟨ZC, hZC, hC⟩ := SieveProfileOperatorLinear.eventually_combination
    S d c r h N hr hh hd hc hcover (δ/2) hdHalf
  obtain ⟨ZE, hZE, hE⟩ := eventually_tail
  refine ⟨max ZF (max ZC ZE), (by linarith : (2:ℝ) ≤ ZF).trans (le_max_left _ _), ?_⟩
  intro z T hz hT hparam
  have hzF : ZF ≤ z := (le_max_left _ _).trans hz
  have hzC : ZC ≤ z := (le_max_left _ _).trans ((le_max_right _ _).trans hz)
  have hzE : ZE ≤ z := (le_max_right _ _).trans ((le_max_right _ _).trans hz)
  have hf := hF z T hzF hT hparam
  have hc := hC z T hzC hT hparam
  have he := hE z T hzE hT
  rw [operator_profile_eq]
  change operator (fun T z => staircase S d c (log T/log z)) T z ≤ _ at hc
  unfold rowBound
  linarith

run_cmd do
  for decl in [``staircase_nonneg, ``profile_nonneg, ``profile_tail_lower,
    ``eventually_tail, ``operator_profile_eq, ``eventually_transition] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL FINITE STAIRCASE PLUS TAIL TRANSITION WITH UNIFORM THRESHOLD"

end SieveProfileTransition
end
