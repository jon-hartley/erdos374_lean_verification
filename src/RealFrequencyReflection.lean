import HarmanProductTail

/-! Reflection of the actual finite Dirichlet products for real coefficients. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace RealFrequencyReflection
open Erdos374.HarmanGram152

theorem vertical_real (s : Finset ℕ) (a : ℕ → ℝ) (σ t : ℝ) :
    verticalDirichlet152 s (fun n => (a n : ℂ)) σ (-t) =
      conj (verticalDirichlet152 s (fun n => (a n : ℂ)) σ t) := by
  unfold verticalDirichlet152
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, Complex.conj_ofReal]
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact Real.pi_ne_zero.symm
  have hpower := Complex.cpow_conj (n : ℂ)
    (-((σ : ℂ) + Complex.I * (t : ℂ))) harg
  have hbase : conj (n : ℂ) = (n : ℂ) := by simp
  rw [hbase] at hpower
  have hexp : conj (-((σ : ℂ) + Complex.I * (t : ℂ))) =
      -((σ : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) := by
    simp only [map_neg, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Complex.ofReal_neg]
    ring
  rw [hexp] at hpower
  exact congrArg (fun z : ℂ => (a n : ℂ) * z) hpower

theorem product_norm_even (sk sm sn : Finset ℕ) (am an : ℕ → ℝ)
    (σ t : ℝ) :
    ‖verticalDirichlet152 sk (fun _ => 1) σ (-t) *
        verticalDirichlet152 sm (fun n => (am n : ℂ)) σ (-t) *
          verticalDirichlet152 sn (fun n => (an n : ℂ)) σ (-t)‖ ^ 2 =
      ‖verticalDirichlet152 sk (fun _ => 1) σ t *
        verticalDirichlet152 sm (fun n => (am n : ℂ)) σ t *
          verticalDirichlet152 sn (fun n => (an n : ℂ)) σ t‖ ^ 2 := by
  have hk : verticalDirichlet152 sk (fun _ => 1) σ (-t) =
      conj (verticalDirichlet152 sk (fun _ => 1) σ t) := by
    simpa using vertical_real sk (fun _ => 1) σ t
  rw [hk, vertical_real sm am, vertical_real sn an, ← map_mul, ← map_mul]
  simp only [Complex.norm_conj]

theorem interval_reflection (f : ℝ → ℝ) (H U : ℝ)
    (hHU : H ≤ U) (heven : ∀ t, f (-t) = f t) :
    (∫ t in Icc (-U) (-H), f t) = ∫ t in Icc H U, f t := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -U ≤ -H by linarith),
    ← intervalIntegral.integral_comp_neg (f := f) (a := H) (b := U)]
  simp only [heven]
  rw [intervalIntegral.integral_of_le hHU, ← integral_Icc_eq_integral_Ioc]

theorem product_negative_eq_positive (sk sm sn : Finset ℕ)
    (am an : ℕ → ℝ) (σ H U : ℝ) (hHU : H ≤ U) :
    (∫ t in Icc (-U) (-H),
      ‖verticalDirichlet152 sk (fun _ => 1) σ t *
        verticalDirichlet152 sm (fun n => (am n : ℂ)) σ t *
          verticalDirichlet152 sn (fun n => (an n : ℂ)) σ t‖ ^ 2) =
    ∫ t in Icc H U,
      ‖verticalDirichlet152 sk (fun _ => 1) σ t *
        verticalDirichlet152 sm (fun n => (am n : ℂ)) σ t *
          verticalDirichlet152 sn (fun n => (an n : ℂ)) σ t‖ ^ 2 := by
  exact interval_reflection _ H U hHU
    (fun t => product_norm_even sk sm sn am an σ t)

end RealFrequencyReflection

#print axioms RealFrequencyReflection.product_negative_eq_positive
run_cmd do
  for target in [``RealFrequencyReflection.vertical_real,
      ``RealFrequencyReflection.product_norm_even,
      ``RealFrequencyReflection.interval_reflection,
      ``RealFrequencyReflection.product_negative_eq_positive] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "REAL FREQUENCY REFLECTION PASSED"
