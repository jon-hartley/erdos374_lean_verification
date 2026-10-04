import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
Scalar absorption for the five-term envelope in the accompanying
written contour proof. No small prime polynomial, smoothed Mellin formula or
zero-free estimate is assumed or proved by the scalar theorem. The retained
medium-log proof is adapted solely as an elementary exponential domination lemma.
This bounded module is Mathlib-only and does not import the full Erdos project.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter
namespace Item1SmoothCapScalar
/-- Adapted from Update152, lines 31240--31263. The original theorem is
`medium_logPower_eventually_small141`; only name/namespace and layout change.
Its argument is an elementary limit, not a PNT or zeta input. -/
private theorem eventually_log_power_small
    (k : ℕ) (c : ℝ) (hc : 0 < c) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) *
        (Real.log x) ^ k < eps := by
  have hroot : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      Real.tendsto_log_atTop
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((10 * k : ℕ) : ℝ) c hc).comp hroot
  have hsmall := (tendsto_order.mp hlim).2 eps heps
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hxsmall hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hpower : ((Real.log x) ^ ((1 : ℝ) / 10)) ^ ((10 * k : ℕ) : ℝ) =
      (Real.log x) ^ k := by
    rw [← Real.rpow_mul hlog0]
    have hexp : ((1 : ℝ) / 10) * ((10 * k : ℕ) : ℝ) = (k : ℝ) := by
      push_cast
      ring
    rw [hexp, Real.rpow_natCast]
  change ((Real.log x) ^ ((1 : ℝ) / 10)) ^ ((10 * k : ℕ) : ℝ) *
    Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) < eps at hxsmall
  rw [hpower] at hxsmall
  simpa only [mul_comm] using hxsmall

def lowerExponent (B : ℕ) : ℕ := 2*B+6

def normalizedBudget (B : ℕ) (a C ell : ℝ) : ℝ :=
  12/ell + 4*(Real.exp (-ell)*ell^(B+1)) +
  (9*(4:ℝ)^9*C)*(Real.exp (-(a/4)*ell^(1/4:ℝ))*ell^(2*B+11)) +
  (216*(4:ℝ)^9*C)/ell^(2*B+1) + 324/ell^2

theorem target_parameters :
    lowerExponent 26001=52008 ∧ 26001+2=26003 ∧
      26001+11=26012 ∧ 2*26001+11=52013 := by
  norm_num [lowerExponent]

/-- Reuse the existing elementary exponential/log-power limit after u=exp ell.
This is not an application of the prime number theorem. -/
theorem eventually_power_exp_small (m : ℕ) (c r eps : ℝ)
    (hc : 0 < c) (hr : (1/10:ℝ) ≤ r) (heps : 0 < eps) :
    ∀ᶠ ell : ℝ in atTop, Real.exp (-c*ell^r)*ell^m ≤ eps := by
  have hh := Real.tendsto_exp_atTop.eventually
    (eventually_log_power_small m c hc eps heps)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with ell he hL
  have hbase : Real.exp (-c*ell^(1/10:ℝ))*ell^m < eps := by
    simpa only [Real.log_exp] using he
  have hp := Real.rpow_le_rpow_of_exponent_le hL hr
  have hecomp : Real.exp (-c*ell^r) ≤ Real.exp (-c*ell^(1/10:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_right hecomp (pow_nonneg (by linarith) m)).trans hbase.le

theorem reciprocal_power_le (ell : ℝ) (k : ℕ) (hL : 1 ≤ ell) (hk : 1 ≤ k) :
    1/ell^k ≤ 1/ell := by
  have hp : ell ≤ ell^k := by
    simpa only [pow_one] using pow_le_pow_right₀ hL hk
  exact one_div_le_one_div_of_le (by linarith : 0 < ell) hp

/-- All five normalized error terms tend to zero; one common threshold suffices.
The analytic derivation of this envelope is written, not fully formalized here. -/
theorem eventually_budget_le_one (B : ℕ) (a C : ℝ) (ha : 0 < a) (hC : 0 < C) :
    ∀ᶠ ell : ℝ in atTop, normalizedBudget B a C ell ≤ 1 := by
  have h2 := eventually_power_exp_small (B+1) 1 1 (1/20)
    (by norm_num) (by norm_num) (by norm_num)
  have h3 := eventually_power_exp_small (2*B+11) (a/4) (1/4)
    (1/(45*(4:ℝ)^9*C)) (by positivity) (by norm_num) (by positivity)
  filter_upwards [h2,h3,eventually_ge_atTop (1620:ℝ),
    eventually_ge_atTop (1080*(4:ℝ)^9*C)] with ell he2 he3 hL hLC
  have hL0 : 0 < ell := by linarith
  have hL1 : 1 ≤ ell := by linarith
  have ht1 : 12/ell ≤ (1/5:ℝ) := (div_le_iff₀ hL0).mpr (by linarith)
  have ht2 : 4*(Real.exp (-ell)*ell^(B+1)) ≤ (1/5:ℝ) := by
    simpa only [Real.rpow_one, neg_mul, one_mul, mul_one_div, show (4:ℝ)/20=1/5 by norm_num] using
      mul_le_mul_of_nonneg_left he2 (by norm_num : (0:ℝ) ≤ 4)
  have ht3 : (9*(4:ℝ)^9*C)*
      (Real.exp (-(a/4)*ell^(1/4:ℝ))*ell^(2*B+11)) ≤ (1/5:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left he3
      (show 0 ≤ 9*(4:ℝ)^9*C by positivity)
    have hid : (9*(4:ℝ)^9*C)*(1/(45*(4:ℝ)^9*C))=(1/5:ℝ) := by
      field_simp [hC.ne']
      <;> ring
    exact hh.trans_eq hid
  have ht4 : (216*(4:ℝ)^9*C)/ell^(2*B+1) ≤ (1/5:ℝ) := by
    have hp := mul_le_mul_of_nonneg_left
      (reciprocal_power_le ell (2*B+1) hL1 (by omega))
      (show 0 ≤ 216*(4:ℝ)^9*C by positivity)
    have hh : (216*(4:ℝ)^9*C)/ell ≤ (1/5:ℝ) :=
      (div_le_iff₀ hL0).mpr (by nlinarith)
    have hp' : (216*(4:ℝ)^9*C)/ell^(2*B+1) ≤ (216*(4:ℝ)^9*C)/ell := by
      simpa only [mul_one_div] using hp
    exact hp'.trans hh
  have ht5 : 324/ell^2 ≤ (1/5:ℝ) := by
    have hp := mul_le_mul_of_nonneg_left
      (reciprocal_power_le ell 2 hL1 (by norm_num)) (by norm_num : (0:ℝ) ≤ 324)
    have hh : (324:ℝ)/ell ≤ (1/5:ℝ) := (div_le_iff₀ hL0).mpr (by linarith)
    have hp' : (324:ℝ)/ell^2 ≤ 324/ell := by
      simpa only [mul_one_div] using hp
    exact hp'.trans hh
  unfold normalizedBudget
  linarith

run_cmd do
  for target in [``eventually_log_power_small, ``target_parameters,
    ``eventually_power_exp_small, ``reciprocal_power_le, ``eventually_budget_le_one] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms eventually_log_power_small
#print axioms eventually_budget_le_one

end Item1SmoothCapScalar
