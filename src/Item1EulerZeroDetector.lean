import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-!
The three-mode Euler positivity inequality for the ACTUAL zeta logarithmic
 derivative. All infinite series are used in Re(s)>1. No zero-free region
left of one, polynomial cap, or assumed positivity statement is an input.
The positive-integer L-series conversion is adapted from the retained
Item1RampDirichlet; it is reproduced here to avoid importing its Mellin chain.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open Complex
open scoped BigOperators
namespace Item1EulerZeroDetector

def F (s : ℂ) : ℂ := -deriv riemannZeta s / riemannZeta s

def term (s : ℂ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt (n+1) : ℂ) *
    Complex.exp (-s * (Real.log (n+1:ℕ) : ℂ))

def realTerm (σ t : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (n+1) *
    Real.exp (-σ * Real.log (n+1:ℕ)) * Real.cos (t * Real.log (n+1:ℕ))

theorem cpow_positive_exp (x : ℝ) (hx : 0 < x) (s : ℂ) :
    (x:ℂ)^s = Complex.exp (s*(Real.log x:ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne')]
  rw [←Complex.ofReal_log hx.le]
  congr 1
  ring

theorem lseries_term_exp (s : ℂ) (n : ℕ) :
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m:ℂ)) s (n+1) =
      term s n := by
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  simp only [LSeries.term,show n+1 ≠ 0 by omega,if_false]
  have hpow := cpow_positive_exp ((n+1:ℕ):ℝ) hn s
  simp only [Complex.ofReal_natCast] at hpow
  rw [hpow,div_eq_mul_inv,←Complex.exp_neg]
  unfold term
  congr 2
  ring

/-- Absolute convergence and the genuine logarithmic-derivative series. -/
theorem hasSum_F (s : ℂ) (hs : 1 < s.re) : HasSum (term s) (F s) := by
  have hi : Summable (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hi1 : Summable (term s) := by
    simpa only [lseries_term_exp] using (summable_nat_add_iff 1).2 hi
  have hzero := hi.tsum_eq_zero_add
  have ht0 : LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)) s 0 = 0 := by
    simp [LSeries.term]
  rw [ht0,zero_add] at hzero
  have hζ := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  change (∑' n, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m:ℂ)) s n) = F s at hζ
  rw [hzero] at hζ
  have he : (∑' n, term s n) = F s := by simpa only [lseries_term_exp] using hζ
  simpa only [he] using hi1.hasSum

theorem term_re (σ t : ℝ) (n : ℕ) :
    (term ((σ:ℂ)+(t:ℂ)*Complex.I) n).re = realTerm σ t n := by
  have hr : (-((σ:ℂ)+(t:ℂ)*Complex.I)*(Real.log (n+1:ℕ):ℂ)).re =
      -σ*Real.log (n+1:ℕ) := by simp
  have hm : (-((σ:ℂ)+(t:ℂ)*Complex.I)*(Real.log (n+1:ℕ):ℂ)).im =
      -(t*Real.log (n+1:ℕ)) := by simp
  simp only [term,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.exp_re,hr,hm,Real.cos_neg,realTerm]
  ring

theorem hasSum_real_F (σ t : ℝ) (hσ : 1 < σ) :
    HasSum (realTerm σ t) (F ((σ:ℂ)+(t:ℂ)*Complex.I)).re := by
  have hh := Complex.hasSum_re (hasSum_F ((σ:ℂ)+(t:ℂ)*Complex.I) (by simpa using hσ))
  simpa only [term_re] using hh

/-- The exact nonnegative trigonometric polynomial, not a numerical sample. -/
theorem trig_identity (θ : ℝ) :
    3+4*Real.cos θ+Real.cos (2*θ) = 2*(1+Real.cos θ)^2 := by
  rw [Real.cos_two_mul]
  ring

theorem three_terms (σ t : ℝ) (n : ℕ) :
    3*realTerm σ 0 n + 4*realTerm σ t n + realTerm σ (2*t) n =
      2*ArithmeticFunction.vonMangoldt (n+1)*Real.exp (-σ*Real.log (n+1:ℕ))*
        (1+Real.cos (t*Real.log (n+1:ℕ)))^2 := by
  unfold realTerm
  simp only [zero_mul,Real.cos_zero,mul_one]
  rw [show (2*t)*Real.log (n+1:ℕ) = 2*(t*Real.log (n+1:ℕ)) by ring,
    Real.cos_two_mul]
  ring

/-- The arithmetic positivity inequality, with only the Re(s)>1 guard. -/
theorem three_mode_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3*(F (σ:ℂ)).re + 4*(F ((σ:ℂ)+(t:ℂ)*Complex.I)).re +
      (F ((σ:ℂ)+((2*t:ℝ):ℂ)*Complex.I)).re := by
  have h0 := hasSum_real_F σ 0 hσ
  have h1 := hasSum_real_F σ t hσ
  have h2 := hasSum_real_F σ (2*t) hσ
  have hsum := ((HasSum.mul_left (3:ℝ) h0).add
    (HasSum.mul_left (4:ℝ) h1)).add h2
  have hn : 0 ≤ ∑' n : ℕ,
      (3*realTerm σ 0 n+4*realTerm σ t n+realTerm σ (2*t) n) := by
    apply tsum_nonneg
    intro n
    rw [three_terms]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
        ArithmeticFunction.vonMangoldt_nonneg) (Real.exp_pos _).le)
      (sq_nonneg _)
  rw [hsum.tsum_eq] at hn
  simpa using hn

#print axioms three_mode_nonneg
run_cmd do
  let targets : List Lean.Name := [
    ``cpow_positive_exp, ``lseries_term_exp, ``hasSum_F, ``term_re,
    ``hasSum_real_F, ``trig_identity, ``three_terms, ``three_mode_nonneg]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Item1EulerZeroDetector
