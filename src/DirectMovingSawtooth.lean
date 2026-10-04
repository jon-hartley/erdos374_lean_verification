import PairFourierResidual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The exact centered sawtooth underlying the moving floor discrepancy. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set intervalIntegral
open scoped Real ENNReal BigOperators

namespace DirectMovingSawtooth
open PairFourier

def sawtooth (n : ℕ) (x : ℝ) : ℂ := ((1/2 - Int.fract (x/n) : ℝ) : ℂ)

theorem measurable (n : ℕ) : Measurable (sawtooth n) := by
  unfold sawtooth
  fun_prop

theorem norm_le_one (n : ℕ) (x : ℝ) : ‖sawtooth n x‖ ≤ 1 := by
  simp only [sawtooth, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [Int.fract_lt_one (x/(n:ℝ))],
    by linarith [Int.fract_nonneg (x/(n:ℝ))]⟩

theorem memLp (n : ℕ) (a b : ℝ) (p : ℝ≥0∞) :
    MemLp (sawtooth n) p (volume.restrict (Ioc a b)) := by
  apply MemLp.of_bound (measurable n).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (norm_le_one n)

theorem intervalIntegrable (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (sawtooth n) volume a b := by
  constructor <;> exact (memLp n _ _ 1).integrable le_rfl

theorem periodic (n : ℕ) (hn : 0<n) : Function.Periodic (sawtooth n) (n:ℝ) := by
  intro x
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  simp only [sawtooth, add_div, div_self hn0, Int.fract_add_one]

theorem discrepancy_eq (n : ℕ) (h x : ℝ) :
    PairFourier.discrepancy n h x = sawtooth n x - sawtooth n (x-h) := by
  rw [PairFourier.discrepancy, SingletonDivisor.discrepancy_eq_fract]
  unfold sawtooth
  push_cast
  ring

theorem eq_affine (n : ℕ) (hn : 0<n) (x : ℝ) (hx0 : 0≤x) (hxn : x<n) :
    sawtooth n x = (1/2:ℂ) - (x:ℂ)/(n:ℂ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  rw [sawtooth, Int.fract_eq_self.mpr ⟨div_nonneg hx0 hnR.le,
    (div_lt_one hnR).mpr hxn⟩]
  push_cast
  rfl

theorem integral_mul_eq_affine (n : ℕ) (hn : 0<n) (f : ℝ→ℂ) :
    (∫x in (0:ℝ)..n, f x * sawtooth n x) =
      ∫x in (0:ℝ)..n, f x * ((1/2:ℂ)-(x:ℂ)/(n:ℂ)) := by
  apply integral_congr_Ioo_of_le (Nat.cast_nonneg n)
  intro x hx
  dsimp only
  rw [eq_affine n hn x hx.1.le hx.2]

theorem integral_eq_zero (n : ℕ) (hn : 0<n) :
    (∫x in (0:ℝ)..n, sawtooth n x) = 0 := by
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have he : (∫x in (0:ℝ)..n, sawtooth n x) =
      Complex.ofReal (∫x in (0:ℝ)..n, (1/2:ℝ)-x/(n:ℝ)) := by
    rw [←intervalIntegral.integral_ofReal]
    apply integral_congr_Ioo_of_le (Nat.cast_nonneg n)
    intro x hx
    dsimp only
    rw [eq_affine n hn x hx.1.le hx.2]
    push_cast
    rfl
  rw [he]
  suffices hi : (∫x in (0:ℝ)..n, (1/2:ℝ)-x/(n:ℝ)) = 0 by
    simp only [hi, Complex.ofReal_zero]
  rw [intervalIntegral.integral_sub (f:=fun _ : ℝ => (1/2:ℝ))
    (g:=fun x : ℝ => x/(n:ℝ)) (continuous_const.intervalIntegrable _ _)
    ((continuous_id.div_const (n:ℝ)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_div, integral_id]
  simp only [sub_zero, zero_pow (by norm_num : (2:ℕ)≠0), smul_eq_mul]
  field_simp
  ring

theorem coefficient_zero (n : ℕ) (hn : 0<n) :
    fourierCoeffOn (show (0:ℝ)<n by exact_mod_cast hn) (sawtooth n) 0 = 0 := by
  rw [PairFourier.coefficient_eq_integral]
  simp only [neg_zero, phase_zero, one_mul, integral_eq_zero n hn, smul_zero]

run_cmd do
  for decl in [``sawtooth, ``measurable, ``norm_le_one, ``memLp, ``intervalIntegrable,
      ``periodic, ``discrepancy_eq, ``eq_affine, ``integral_mul_eq_affine,
      ``integral_eq_zero, ``coefficient_zero] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "CENTERED SAWTOOTH EXACT FLOOR DISCREPANCY AND ZERO MEAN PASSED"

end DirectMovingSawtooth
