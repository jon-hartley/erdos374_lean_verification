import Erdos374_AnalyticClosure150
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! October 2, 2026. UNCOMPILED proof-body draft.
The PNT proof is called internally; no PNT argument, new axiom, or cap argument
is introduced. The generic uniformization lemma is instantiated below twice.
The original pinned baseline and its external theorem closure remain required. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open Filter Asymptotics
namespace Item1UniformLogArithmetic
open Erdos374.RemainingAnalytic115.RemainingAnalytic141

/-- Every fixed log-weighted relative psi remainder, using the existing PNT term. -/
theorem psi_log_weight (m : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ u : ℝ in atTop,
      |Chebyshev.psi u-u| * (Real.log u)^m ≤ eps*u := by
  obtain ⟨c, hc, hPNT⟩ := Erdos374.AnalyticClosure150.pntInput
  obtain ⟨C, hC, hbound⟩ := Asymptotics.isBigO_iff'.mp hPNT
  have hw := medium_logPower_eventually_small141 m c hc (eps/C) (by positivity)
  filter_upwards [hbound, hw, eventually_ge_atTop (1:ℝ)] with u hu hw hu1
  have hu0 : 0 ≤ u := by linarith
  have hl : 0 ≤ (Real.log u)^m := pow_nonneg (Real.log_nonneg hu1) m
  have hr0 : 0 ≤ u*Real.exp (-c*(Real.log u)^((1:ℝ)/10)) := by positivity
  have herr : |Chebyshev.psi u-u| ≤
      C*(u*Real.exp (-c*(Real.log u)^((1:ℝ)/10))) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hu
  have hcancel : C*(eps/C)=eps := by field_simp [ne_of_gt hC]
  have hsmall := mul_le_mul_of_nonneg_left hw.le hC.le
  rw [hcancel] at hsmall
  calc
    _ ≤ (C*(u*Real.exp (-c*(Real.log u)^((1:ℝ)/10))))*(Real.log u)^m :=
      mul_le_mul_of_nonneg_right herr hl
    _ = u*(C*(Real.exp (-c*(Real.log u)^((1:ℝ)/10))*(Real.log u)^m)) := by ring
    _ ≤ u*eps := mul_le_mul_of_nonneg_left hsmall hu0
    _ = eps*u := by ring

/-- The proper-prime-power remainder is elementary; this proof does not use PNT. -/
theorem prime_power_log_weight (m : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ u : ℝ in atTop,
      |Chebyshev.psi u-Chebyshev.theta u| *(Real.log u)^m ≤ eps*u := by
  have h := primePower_logPower_eventually_small141 m eps heps
  filter_upwards [h, eventually_ge_atTop (1:ℝ)] with u hu hu1
  exact (mul_le_mul_of_nonneg_right
    (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hu1)
    (pow_nonneg (Real.log_nonneg hu1) m)).trans hu

/-- Uniformity on an entire moving half-line. The threshold is chosen before u. -/
theorem uniform_above_power (E : ℝ → ℝ) (hE : ∀ u, 0 ≤ E u) (m : ℕ)
    (hweighted : ∀ eps : ℝ, 0 < eps →
      ∀ᶠ u : ℝ in atTop, E u*(Real.log u)^m ≤ eps*u)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ X : ℝ in atTop, ∀ u : ℝ, X^((1:ℝ)/7) ≤ u →
      E u*(1+Real.log X)^m ≤ eps*u := by
  have h8 : (0:ℝ) < 8^m := by positivity
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    (hweighted (eps/(8:ℝ)^m) (by positivity))
  have hroot : Tendsto (fun X : ℝ => X^((1:ℝ)/7)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/7)
  have hthreshold := hroot.eventually (eventually_ge_atTop A)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (7:ℝ))
  filter_upwards [hthreshold, hlog, eventually_ge_atTop (2:ℝ)] with X hXA hLX hX
  intro u hu
  have hXp : 0<X := by linarith
  have hup : 0<u := (Real.rpow_pos_of_pos hXp _).trans_le hu
  have hlogs := Real.log_le_log (Real.rpow_pos_of_pos hXp _) hu
  rw [Real.log_rpow hXp] at hlogs
  have hlu : 0 ≤ Real.log u := by linarith
  have hlX : 0 ≤ 1+Real.log X := by linarith
  have hcmp : 1+Real.log X ≤ 8*Real.log u := by linarith
  have hp := pow_le_pow_left₀ hlX hcmp m
  rw [mul_pow] at hp
  have he := hA u (hXA.trans hu)
  have hmul := mul_le_mul_of_nonneg_left he (le_of_lt h8)
  have hcancel : (8:ℝ)^m*((eps/(8:ℝ)^m)*u)=eps*u := by
    field_simp [ne_of_gt h8]
  rw [hcancel] at hmul
  calc
    _ ≤ E u*((8:ℝ)^m*(Real.log u)^m) :=
      mul_le_mul_of_nonneg_left hp (hE u)
    _ = (8:ℝ)^m*(E u*(Real.log u)^m) := by ring
    _ ≤ eps*u := hmul

/-- Closed arithmetic instance of the uniform moving-range theorem. -/
theorem uniform_psi (m : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∀ᶠ X : ℝ in atTop, ∀ u : ℝ, X^((1:ℝ)/7) ≤ u →
      |Chebyshev.psi u-u| *(1+Real.log X)^m ≤ eps*u :=
  uniform_above_power (fun u => |Chebyshev.psi u-u|) (fun _ => abs_nonneg _) m
    (psi_log_weight m) eps heps

/-- Closed elementary instance, independent of the PNT proof. -/
theorem uniform_prime_power_gap (m : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∀ᶠ X : ℝ in atTop, ∀ u : ℝ, X^((1:ℝ)/7) ≤ u →
      |Chebyshev.psi u-Chebyshev.theta u| *(1+Real.log X)^m ≤ eps*u :=
  uniform_above_power (fun u => |Chebyshev.psi u-Chebyshev.theta u|)
    (fun _ => abs_nonneg _) m (prime_power_log_weight m) eps heps

run_cmd do
  for target in [``psi_log_weight, ``prime_power_log_weight,
      ``uniform_above_power, ``uniform_psi, ``uniform_prime_power_gap] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "UNIFORM LOG ARITHMETIC: five original theorem guards passed."

end Item1UniformLogArithmetic
