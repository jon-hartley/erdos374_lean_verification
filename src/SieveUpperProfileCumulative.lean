import SieveProfileOperatorTransfer
import SieveStoppingRecurrence

/-! Actual one-prime Euler-weighted cumulative masses above the cubic
parent level. The cumulative endpoint is closed; the prime pool is strict. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace SieveUpperProfileCumulative
open SieveStoppingExpansion SieveProfileOperatorCumulative PrimeEulerProfileIntervals

def onePrime (f : ℝ → ℝ → ℝ) (T z : ℝ) : ℝ :=
  ∑ p ∈ SieveSmallWeights.pool z,
    (PrimeEulerMass.weight p/primeEuler z)*f (T/(p:ℝ)) (p:ℝ)

def cumulative (c r : ℝ) : ℝ := max 0 ((c+1)/r-1)

def error (c e : ℝ) : ℝ := (3*(c+1)+(c+1)^2)*e+3*(c+1)^2*e^2

theorem weight_nonneg (p : ℕ) (z : ℝ) : 0 ≤ PrimeEulerMass.weight p/primeEuler z :=
  div_nonneg (PrimeEulerMass.weight_nonneg p) (SieveEulerRatio.euler_pos z).le

theorem level_ge (T z : ℝ) (hz : 2 ≤ z) (hT : z^3 ≤ T) : z ≤ T := by
  have h := mul_nonneg (sq_nonneg z) (show 0 ≤ z-1 by linarith)
  nlinarith

theorem parameter_ge_three (T z : ℝ) (hz : 2 ≤ z) (hT : z^3 ≤ T) :
    3 ≤ log T/log z := by
  have hlog := log_le_log (pow_pos (by linarith : 0 < z) 3) hT
  rw [log_pow] at hlog
  apply (le_div_iff₀ (log_pos (by linarith : 1 < z))).mpr
  norm_num at hlog ⊢
  exact hlog

theorem all_gates (T z : ℝ) (hT : z^3 ≤ T) (p : ℕ)
    (hp : p ∈ SieveSmallWeights.pool z) : (p:ℝ)^3 < T :=
  (pow_lt_pow_left₀ ((SieveSmallWeights.mem_pool z p).mp hp).2
    (Nat.cast_nonneg p) (by decide : 3 ≠ 0)).trans_le hT

theorem indicator_eq_innerMass (T z c : ℝ) (hT : z^3 ≤ T) :
    onePrime (fun T z => if log T/log z ≤ c then 1 else 0) T z = innerMass T z c := by
  have hs : PrimeEulerAcceptedInner.acceptedPrimes T z = SieveSmallWeights.pool z := by
    apply Finset.filter_eq_self.mpr
    exact fun p hp => all_gates T z hT p hp
  rw [innerMass, hs, onePrime]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

theorem shape_eq_cumulative (c r : ℝ) (hr : 3 ≤ r) : shape c r = cumulative c r := by
  unfold shape cumulative
  rw [max_eq_right hr]
  congr 1
  field_simp

theorem cumulative_le_area (c r : ℝ) (hc : 2 ≤ c) (hr : 3 ≤ r) :
    cumulative c r ≤ (c-2)/3 := by
  unfold cumulative
  apply max_le (by linarith)
  have hh := div_le_div_of_nonneg_left (by linarith : 0 ≤ c+1)
    (by norm_num : (0:ℝ) < 3) hr
  linarith

theorem cumulative_bound (T z c : ℝ) (hz : 2 ≤ z) (hT : z^3 ≤ T)
    (hc : 2 ≤ c) (ha : 2 ≤ lowerCut T c) :
    onePrime (fun T z => if log T/log z ≤ c then 1 else 0) T z ≤
      cumulative c (log T/log z)+error c (epsilon z) := by
  have hr := parameter_ge_three T z hz hT
  have he : 0 ≤ epsilon z := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le
    (log_pos (by linarith : 1 < z)).le
  have hb := innerMass_bound T z c hz (level_ge T z hz hT) hc ha
  have hs := mul_le_mul_of_nonneg_left (shape_le c (log T/log z) hc (by linarith))
    (show 0 ≤ 3*epsilon z by positivity)
  rw [indicator_eq_innerMass T z c hT]
  rw [← shape_eq_cumulative c (log T/log z) hr]
  unfold error
  nlinarith

/-- The arithmetic error tends to zero uniformly in every parent level
above z cubed. The cutoff is chosen before both z and T. -/
theorem eventually_cumulative (c : ℝ) (hc : 2 ≤ c) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      onePrime (fun T z => if log T/log z ≤ c then 1 else 0) T z ≤
        cumulative c (log T/log z)+δ := by
  have hcont : Continuous (error c) := by unfold error; fun_prop
  have ht := hcont.continuousAt.tendsto.comp SieveProfileOperatorTransfer.epsilon_tendsto
  have he : ∀ᶠ z : ℝ in atTop, error c (epsilon z) < δ :=
    ht.eventually_lt_const (by simpa [error] using hδ)
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp he
  let Z := max 2 (max Z₀ (exp ((c+1)*log 2)))
  refine ⟨Z, le_max_left _ _, ?_⟩
  intro z T hz hT
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hz
  have hza : exp ((c+1)*log 2) ≤ z :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hz)
  have ha := SieveProfileOperatorTransfer.two_le_cut z (c+1) (by linarith) hza
  have hTz := level_ge T z hz2 hT
  have haT : 2 ≤ lowerCut T c := ha.trans (exp_le_exp.mpr
    (div_le_div_of_nonneg_right (log_le_log (by linarith : 0 < z) hTz) (by linarith)))
  exact (cumulative_bound T z c hz2 hT hc haT).trans
    (add_le_add le_rfl (hZ₀ z ((le_max_left _ _).trans ((le_max_right _ _).trans hz))).le)

run_cmd do
  for decl in [``weight_nonneg, ``level_ge, ``parameter_ge_three, ``all_gates,
      ``indicator_eq_innerMass, ``shape_eq_cumulative, ``cumulative_le_area,
      ``cumulative_bound, ``eventually_cumulative] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ONE-PRIME CUMULATIVE MASS WITH UNIFORM VANISHING ERROR"
end SieveUpperProfileCumulative
end
