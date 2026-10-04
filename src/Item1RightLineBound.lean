import Item1ZetaDirichletSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
UNCOMPILED PROOF-BODY DRAFT. Quantitative bound on the ACTUAL logarithmic
zeta derivative on Re(s)=1+c. No PNT, strip, cap, or unspecified tail bound.
All positive integers are indexed by n+1, consistently with the Mellin parent.
-/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace Item1RightLineBound
open Item1RampDirichlet

/-- An elementary p-series estimate, including its first term. -/
theorem positive_pseries (d : ℝ) (hd : 0 < d) :
    Summable (fun n : ℕ => ((n+1:ℕ):ℝ)^(-1-d)) ∧
      (∑' n : ℕ, ((n+1:ℕ):ℝ)^(-1-d)) ≤ 1+1/d := by
  let f : ℝ → ℝ := fun x => x^(-1-d)
  have ha : AntitoneOn f (Ici (1:ℝ)) := by
    intro x hx y hy hxy
    change 1 ≤ x at hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)
  have hi : IntegrableOn f (Ioi (1:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hn : ∀ x ∈ Ioi (1:ℝ), 0 ≤ f x := by
    intro x hx
    change 1 < x at hx
    exact Real.rpow_nonneg (by linarith) _
  have hs : Summable (fun n : ℕ => f n) :=
    AntitoneOn.summable_of_integrableOn_Ioi (N := 1)
      (by simpa only [Nat.cast_one] using ha)
      (by simpa only [Nat.cast_one] using hi)
      (by simpa only [Nat.cast_one] using hn)
  have hs1 : Summable (fun n : ℕ => f (n+1:ℕ)) := (summable_nat_add_iff 1).2 hs
  have ht := AntitoneOn.tsum_comp_add_le_integral (f := f) 1
    (by simpa only [Nat.cast_one] using ha)
    (by simpa only [Nat.cast_one] using hi)
    (by simpa only [Nat.cast_one] using hn)
  simp only [Nat.cast_one] at ht
  have he : (∫ x in Ioi (1:ℝ), f x) = 1/d := by
    dsimp only [f]
    rw [integral_Ioi_rpow_of_lt (by linarith : -1-d < -1) (by norm_num)]
    simp only [Real.one_rpow]
    rw [show -1-d+1 = -d by ring]
    simp
  rw [he] at ht
  refine ⟨hs1, ?_⟩
  have hh := hs1.tsum_eq_zero_add
  simp only [Nat.zero_add, Nat.cast_one, f, Real.one_rpow] at hh
  rw [hh]
  exact add_le_add le_rfl ht

/-- The elementary inequality log x <= (2/c) x^(c/2). -/
theorem log_le_half_power (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    Real.log x ≤ (2/c)*x^(c/2) := by
  have hp : 0 < x^(c/2) := Real.rpow_pos_of_pos hx _
  have hh := Real.log_le_sub_one_of_pos hp
  rw [Real.log_rpow hx] at hh
  apply (mul_le_mul_iff_right₀ (show 0<c/2 by linarith)).mp
  calc
    (c/2)*Real.log x ≤ x^(c/2) := by linarith
    _ = (c/2)*((2/c)*x^(c/2)) := by field_simp

/-- One nonnegative real summand of the absolute Mangoldt Dirichlet series. -/
def absoluteTerm (c : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (n+1) *
    Real.exp (-(1+c)*Real.log (n+1:ℕ))

theorem absoluteTerm_nonneg (c : ℝ) (n : ℕ) : 0 ≤ absoluteTerm c n := by
  unfold absoluteTerm
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le

theorem absoluteTerm_le (c : ℝ) (hc : 0 < c) (n : ℕ) :
    absoluteTerm c n ≤ (2/c)*((n+1:ℕ):ℝ)^(-1-c/2) := by
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  have hl := (ArithmeticFunction.vonMangoldt_le_log (n := n+1)).trans
    (log_le_half_power (n+1:ℕ) c hn hc)
  have hh := mul_le_mul_of_nonneg_right hl
    (Real.exp_pos (-(1+c)*Real.log (n+1:ℕ))).le
  convert hh using 1
  · rfl
  · rw [Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hn]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring

theorem absoluteSeries_summable (c : ℝ) (hc : 0 < c) :
    Summable (absoluteTerm c) := by
  have hp := (positive_pseries (c/2) (by linarith)).1
  exact Summable.of_nonneg_of_le (absoluteTerm_nonneg c)
    (absoluteTerm_le c hc) (hp.mul_left (2/c))

/-- All positive terms, not a truncated sum or numerical evaluation of zeta. -/
theorem absoluteSeries_le (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (∑' n : ℕ, absoluteTerm c n) ≤ 6/c^2 := by
  have hp := positive_pseries (c/2) (by linarith)
  have hm := Summable.tsum_le_tsum (absoluteTerm_le c hc)
    (absoluteSeries_summable c hc) (hp.1.mul_left (2/c))
  rw [tsum_mul_left] at hm
  have he := mul_le_mul_of_nonneg_left hp.2 (by positivity : 0 ≤ 2/c)
  apply hm.trans (he.trans _)
  have hid : (2/c)*(1+1/(c/2)) = (2*c+4)/c^2 := by
    field_simp [hc.ne']
    <;> ring
  rw [hid]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg c)

/-- Uniform in y, including y=0. This is a right-half-plane theorem only. -/
theorem zetaLogDeriv_right_bound (c y : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ‖zetaLogDeriv (1+(c:ℂ)+(y:ℂ)*Complex.I)‖ ≤ 6/c^2 := by
  let b : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt (n+1):ℂ)*
    Complex.exp (-(1+(c:ℂ)+(y:ℂ)*Complex.I)*(Real.log (n+1:ℕ):ℂ))
  have he (n : ℕ) : ‖b n‖ = absoluteTerm c n := by
    simp only [b, absoluteTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.norm_exp]
    congr 2
    simp
  have hb : Summable (fun n => ‖b n‖) := by
    simp_rw [he]
    exact absoluteSeries_summable c hc
  have hz := logarithmic_derivative_series (1+(c:ℂ)+(y:ℂ)*Complex.I)
    (by simpa using hc)
  rw [← hz]
  change ‖∑' n, b n‖ ≤ _
  have hn := norm_tsum_le_tsum_norm hb
  simp_rw [he] at hn
  exact hn.trans (absoluteSeries_le c hc hc1)

end Item1RightLineBound

run_cmd do
  for target in [
    ``Item1RightLineBound.positive_pseries,
    ``Item1RightLineBound.log_le_half_power,
    ``Item1RightLineBound.absoluteTerm_nonneg,
    ``Item1RightLineBound.absoluteTerm_le,
    ``Item1RightLineBound.absoluteSeries_summable,
    ``Item1RightLineBound.absoluteSeries_le,
    ``Item1RightLineBound.zetaLogDeriv_right_bound] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1RightLineBound.zetaLogDeriv_right_bound

