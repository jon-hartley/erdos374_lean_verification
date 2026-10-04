import Item1CenterLogBound
import Mathlib.Tactic

/-!
Finite Blaschke factors and the sign of their center logarithmic
 derivatives. The roots are indexed by Fin n, so repetitions represent
 multiplicities and are NOT removed. This file does not yet extract all zeros
of an arbitrary holomorphic function. Its supplied remaining factor q must
be nonzero and satisfy the stated relative growth bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
open Set Metric Complex
open scoped BigOperators ComplexConjugate
namespace Item1FiniteZeroCharges

/-- A Blaschke ZERO factor; the canonicalFactor in Mathlib is its reciprocal. -/
def blaschke (R : ℝ) (a z : ℂ) : ℂ :=
  (R:ℂ)*(z-a) / ((R:ℂ)^2-conj a*z)

def charge (R : ℝ) (a : ℂ) : ℝ :=
  -a.re * (1/Complex.normSq a - 1/R^2)

def factored {n : ℕ} (q : ℂ → ℂ) (R : ℝ) (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  q z * ∏ i, blaschke R (a i) z

theorem blaschke_zero (R : ℝ) (a : ℂ) (hR : R ≠ 0) :
    blaschke R a 0 = -a/(R:ℂ) := by
  have hRc : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  unfold blaschke
  field_simp [hRc]
  ring

theorem blaschke_zero_ne (R : ℝ) (a : ℂ) (hR : R ≠ 0) (ha : a ≠ 0) :
    blaschke R a 0 ≠ 0 := by
  rw [blaschke_zero R a hR]
  exact div_ne_zero (neg_ne_zero.mpr ha) (by exact_mod_cast hR)

theorem blaschke_differentiable_zero (R : ℝ) (a : ℂ) (hR : R ≠ 0) :
    DifferentiableAt ℂ (blaschke R a) 0 := by
  have hden : (R:ℂ)^2-conj a*(0:ℂ) ≠ 0 := by
    simp only [mul_zero,sub_zero]
    exact pow_ne_zero 2 (by exact_mod_cast hR)
  have hn : DifferentiableAt ℂ (fun z : ℂ => (R:ℂ)*(z-a)) 0 := by fun_prop
  have hd : DifferentiableAt ℂ (fun z : ℂ => (R:ℂ)^2-conj a*z) 0 := by fun_prop
  exact hn.div hd hden

theorem logDeriv_blaschke_zero (R : ℝ) (a : ℂ) (hR : R ≠ 0) (ha : a ≠ 0) :
    logDeriv (blaschke R a) 0 = -1/a+conj a/(R:ℂ)^2 := by
  have hRc : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  have hn : HasDerivAt (fun z : ℂ => (R:ℂ)*(z-a)) (R:ℂ) 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).sub_const a).const_mul (R:ℂ)
  have hd : HasDerivAt (fun z : ℂ => (R:ℂ)^2-conj a*z) (-conj a) 0 := by
    simpa using (((hasDerivAt_id (0:ℂ)).const_mul (conj a)).const_sub ((R:ℂ)^2))
  have hnum : (R:ℂ)*((0:ℂ)-a) ≠ 0 := by simp [hRc,ha]
  have hden : (R:ℂ)^2-conj a*(0:ℂ) ≠ 0 := by simp [hRc]
  change logDeriv (fun z : ℂ => (R:ℂ)*(z-a)/((R:ℂ)^2-conj a*z)) 0 = _
  rw [logDeriv_fun_div 0 hnum hden hn.differentiableAt hd.differentiableAt,
    logDeriv_apply,logDeriv_apply,hn.deriv,hd.deriv]
  field_simp [hRc,ha]
  ring

theorem logDeriv_blaschke_re (R : ℝ) (a : ℂ) (hR : R ≠ 0) (ha : a ≠ 0) :
    (logDeriv (blaschke R a) 0).re = charge R a := by
  rw [logDeriv_blaschke_zero R a hR ha]
  rw [←Complex.ofReal_pow,Complex.add_re,Complex.div_ofReal_re,Complex.conj_re]
  simp only [neg_div,one_div,Complex.neg_re,Complex.inv_re,charge]
  ring

/-- Roots left of the center make NONNEGATIVE contributions to f'/f. -/
theorem charge_nonneg (R : ℝ) (a : ℂ)
    (hR : 0 < R) (ha : 0 < Complex.normSq a)
    (haR : Complex.normSq a ≤ R^2) (hare : a.re ≤ 0) :
    0 ≤ charge R a := by
  unfold charge
  apply mul_nonneg (by linarith)
  exact sub_nonneg.mpr (one_div_le_one_div_of_le ha haR)

theorem aligned_charge (R q : ℝ) (hR : R ≠ 0) (hq : q ≠ 0) :
    charge R (-(q:ℂ)) = 1/q-q/R^2 := by
  simp [charge,Complex.normSq]
  field_simp [hR,hq]

/-- Finite products preserve every repeated root contribution. -/
theorem factored_logDeriv {n : ℕ} (q : ℂ → ℂ) (R : ℝ) (a : Fin n → ℂ)
    (hR : R ≠ 0) (ha : ∀ i, a i ≠ 0) (hq0 : q 0 ≠ 0)
    (hqd : DifferentiableAt ℂ q 0) :
    logDeriv (factored q R a) 0 = logDeriv q 0 +
      ∑ i, logDeriv (blaschke R (a i)) 0 := by
  have hp : (∏ i, blaschke R (a i) (0:ℂ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => blaschke_zero_ne R (a i) hR (ha i))
  have hpd : DifferentiableAt ℂ (fun z => ∏ i, blaschke R (a i) z) 0 := by
    exact DifferentiableAt.fun_finsetProd
      (fun i _ => blaschke_differentiable_zero R (a i) hR)
  change logDeriv (fun z => q z * ∏ i, blaschke R (a i) z) 0 = _
  rw [logDeriv_fun_mul 0 hq0 hp hqd hpd]
  congr 1
  exact logDeriv_fun_prod
    (fun i _ => blaschke_zero_ne R (a i) hR (ha i))
    (fun i _ => blaschke_differentiable_zero R (a i) hR)

/-- A supplied zero-stripped factorization yields the local detector.
Automatic extraction from a general function is a separate, unencoded step. -/
theorem factorized_detector {n : ℕ} (q : ℂ → ℂ) (R M : ℝ) (a : Fin n → ℂ)
    (hR : 0 < R) (hM : 0 < M) (ha : ∀ i, a i ≠ 0)
    (hqd : DifferentiableOn ℂ q (ball 0 R))
    (hqn : ∀ z ∈ ball (0:ℂ) R, q z ≠ 0)
    (hqb : ∀ z ∈ ball (0:ℂ) R, ‖q z‖ ≤ Real.exp M * ‖q 0‖) :
    -(logDeriv (factored q R a) 0).re ≤ 4*M/R - ∑ i, charge R (a i) := by
  have h0 : (0:ℂ) ∈ ball 0 R := by simpa using hR
  have hc := Item1CenterLogBound.center_logDeriv_bound q R M hR hM hqd hqn hqb
  have he := factored_logDeriv q R a hR.ne' ha (hqn 0 h0)
    (hqd.differentiableAt (isOpen_ball.mem_nhds h0))
  rw [he,Complex.add_re,Complex.re_sum]
  simp_rw [logDeriv_blaschke_re R _ hR.ne' (ha _)]
  have hb : -(logDeriv q 0).re ≤ ‖logDeriv q 0‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  linarith

/-- Retain one aligned zero and only drop other NONNEGATIVE charges. -/
theorem one_zero_detector {n : ℕ} (q : ℂ → ℂ) (R M u : ℝ) (a : Fin n → ℂ)
    (i : Fin n) (hR : 0 < R) (hM : 0 < M) (hu : 0 < u)
    (ha : ∀ k, a k ≠ 0)
    (han : ∀ k, 0 < Complex.normSq (a k))
    (haR : ∀ k, Complex.normSq (a k) ≤ R^2)
    (hare : ∀ k, (a k).re ≤ 0) (hai : a i = -(u:ℂ))
    (hqd : DifferentiableOn ℂ q (ball 0 R))
    (hqn : ∀ z ∈ ball (0:ℂ) R, q z ≠ 0)
    (hqb : ∀ z ∈ ball (0:ℂ) R, ‖q z‖ ≤ Real.exp M * ‖q 0‖) :
    -(logDeriv (factored q R a) 0).re ≤ 4*M/R-1/u+u/R^2 := by
  have hd := factorized_detector q R M a hR hM ha hqd hqn hqb
  have hc : charge R (a i) ≤ ∑ k, charge R (a k) := by
    exact Finset.single_le_sum (fun k _ => charge_nonneg R (a k) hR
      (han k) (haR k) (hare k)) (Finset.mem_univ i)
  rw [hai,aligned_charge R u hR.ne' hu.ne'] at hc
  linarith

end Item1FiniteZeroCharges

run_cmd do
  for target in [``Item1FiniteZeroCharges.blaschke_zero,
    ``Item1FiniteZeroCharges.blaschke_zero_ne,
    ``Item1FiniteZeroCharges.blaschke_differentiable_zero,
    ``Item1FiniteZeroCharges.logDeriv_blaschke_zero,
    ``Item1FiniteZeroCharges.logDeriv_blaschke_re,
    ``Item1FiniteZeroCharges.charge_nonneg,
    ``Item1FiniteZeroCharges.aligned_charge,
    ``Item1FiniteZeroCharges.factored_logDeriv,
    ``Item1FiniteZeroCharges.factorized_detector,
    ``Item1FiniteZeroCharges.one_zero_detector] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1FiniteZeroCharges.blaschke_zero
#print axioms Item1FiniteZeroCharges.blaschke_zero_ne
#print axioms Item1FiniteZeroCharges.blaschke_differentiable_zero
#print axioms Item1FiniteZeroCharges.logDeriv_blaschke_zero
#print axioms Item1FiniteZeroCharges.logDeriv_blaschke_re
#print axioms Item1FiniteZeroCharges.charge_nonneg
#print axioms Item1FiniteZeroCharges.aligned_charge
#print axioms Item1FiniteZeroCharges.factored_logDeriv
#print axioms Item1FiniteZeroCharges.factorized_detector
#print axioms Item1FiniteZeroCharges.one_zero_detector
