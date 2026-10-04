import Item1PositiveStripDefinitions
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-! The original three Dirichlet-series lemmas, kept under their original
namespace so the right-line estimate does not require Mellin inversion. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace Item1RampDirichlet

theorem cpow_positive_exp (x : ℝ) (hx : 0 < x) (s : ℂ) :
    (x:ℂ)^s = Complex.exp (s*(Real.log x:ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne')]
  rw [←Complex.ofReal_log hx.le]
  congr 1
  ring

theorem lseries_term_exp (s : ℂ) (n : ℕ) :
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m:ℂ)) s (n+1) =
      (ArithmeticFunction.vonMangoldt (n+1):ℂ)*
        Complex.exp (-s*(Real.log (n+1:ℕ):ℂ)) := by
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  simp only [LSeries.term,show n+1 ≠ 0 by omega,ite_false]
  have hpow := cpow_positive_exp (n+1:ℕ) hn s
  simp only [Complex.ofReal_natCast] at hpow
  rw [hpow,div_eq_mul_inv,←Complex.exp_neg]
  congr 2
  ring

theorem logarithmic_derivative_series (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt (n+1):ℂ)*
      Complex.exp (-s*(Real.log (n+1:ℕ):ℂ))) = zetaLogDeriv s := by
  have hi : Summable (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hzero := hi.tsum_eq_zero_add
  have hterm0 : LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)) s 0 = 0 := by
    simp [LSeries.term]
  rw [hterm0,zero_add] at hzero
  have hζ := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  change (∑' n, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m:ℂ)) s n) =
    zetaLogDeriv s at hζ
  rw [hzero] at hζ
  simpa only [lseries_term_exp] using hζ

end Item1RampDirichlet

run_cmd do
  for target in [``Item1RampDirichlet.cpow_positive_exp,
      ``Item1RampDirichlet.lseries_term_exp,
      ``Item1RampDirichlet.logarithmic_derivative_series] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "DIRICHLET SERIES HELPER PASSED: three original theorem guards."
