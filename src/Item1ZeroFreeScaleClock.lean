import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Elementary scalar choices for the shrinking zeta disks.
The twelfth-root coordinate makes the depth, radius, and growth comparisons
integer-power calculations. This file proves no estimate about zeta. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
open Filter
namespace Item1ZeroFreeScaleClock

def clock (t : ℝ) : ℝ := (Real.log t) ^ (1/12:ℝ)
def step (x : ℝ) : ℝ := 1/x^9
def radius (x : ℝ) : ℝ := 1/(8*x^8)
def growth (A : ℕ) (x : ℝ) : ℝ := (12*(A+2):ℕ)*Real.log x

theorem clock_pos (t : ℝ) (ht : 1<t) : 0<clock t :=
  Real.rpow_pos_of_pos (Real.log_pos ht) _

theorem clock_pow (t : ℝ) (ht : 1<t) (n : ℕ) :
    (clock t)^n=(Real.log t)^((n:ℝ)/12) := by
  rw [clock,←Real.rpow_natCast,←Real.rpow_mul (Real.log_pos ht).le]
  congr 1
  ring

theorem clock_identities (t : ℝ) (ht : 1<t) :
    (clock t)^12=Real.log t ∧
    (clock t)^8=(Real.log t)^(2/3:ℝ) ∧
    (clock t)^9=(Real.log t)^(3/4:ℝ) := by
  constructor
  · simpa using clock_pow t ht 12
  constructor
  · convert clock_pow t ht 8 using 1 <;> norm_num
  · convert clock_pow t ht 9 using 1 <;> norm_num

theorem clock_tendsto : Tendsto clock atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/12)).comp Real.tendsto_log_atTop

theorem pow_twelve_rpow (x : ℝ) (hx : 0<x) :
    (x^12)^(2/3:ℝ)=x^8 := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hx.le]
  norm_num

theorem exp_growth (A : ℕ) (x : ℝ) (hx : 0<x) :
    Real.exp (growth A x)=x^(12*(A+2)) := by
  rw [growth, mul_comm,←Real.rpow_def_of_pos hx,Real.rpow_natCast]

theorem log_le_two_sqrt (x : ℝ) (hx : 0<x) :
    Real.log x≤2*Real.sqrt x := by
  have hs := Real.sqrt_pos.mpr hx
  have he : Real.log x=2*Real.log (Real.sqrt x) := by
    rw [←Real.sq_sqrt hx.le,Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_le_sub_one_of_pos hs]

theorem scale_guards (A : ℕ) (x : ℝ) (hx : 64≤x) :
    0<step x ∧ step x≤1/2 ∧ 0<radius x ∧ radius x≤1/8 ∧
      8*step x≤radius x ∧ 0<growth A x := by
  have hxp : 0<x := by linarith
  have hx1 : 1≤x := by linarith
  have hx8 : 1≤x^8 := one_le_pow₀ hx1
  have hx9 : x≤x^9 := by
    simpa only [pow_one] using pow_le_pow_right₀ hx1 (by norm_num : 1≤9)
  refine ⟨by unfold step; positivity,?_,by unfold radius; positivity,?_,?_,?_⟩
  · unfold step
    apply (div_le_iff₀ (pow_pos hxp 9)).mpr
    linarith
  · unfold radius
    apply (div_le_iff₀ (by positivity : 0<8*x^8)).mpr
    linarith
  · have hratio : 8*step x/radius x=64/x := by
      unfold step radius
      field_simp [hxp.ne']
      <;> ring
    apply (div_le_one (by unfold radius; positivity)).mp
    rw [hratio]
    exact (div_le_one hxp).mpr hx
  · unfold growth
    exact mul_pos (by positivity) (Real.log_pos (by linarith))

theorem budget_identity (A : ℕ) (x : ℝ) (hx : x≠0) :
    40*growth A x*step x/radius x=
      3840*((A:ℝ)+2)*Real.log x/x := by
  unfold growth step radius
  push_cast
  field_simp [hx]
  <;> ring

/-- An explicit scalar sufficient condition; not an arithmetic starting height. -/
theorem budget_of_square (A : ℕ) (x : ℝ)
    (hx : (30720*((A:ℝ)+2))^2≤x) :
    40*growth A x*step x/radius x≤1/4 := by
  let Q : ℝ := 30720*((A:ℝ)+2)
  have hQ : 0<Q := by unfold Q; positivity
  have hxp : 0<x := (sq_pos_of_pos hQ).trans_le hx
  have hsq := Real.sq_sqrt hxp.le
  have hsr : Q≤Real.sqrt x := by
    have hn := Real.sqrt_nonneg x
    change Q^2≤x at hx
    nlinarith
  have hlog : 15360*((A:ℝ)+2)*Real.log x≤x := by
    have hh := mul_le_mul_of_nonneg_left (log_le_two_sqrt x hxp)
      (by positivity : 0≤15360*((A:ℝ)+2))
    have hm := mul_le_mul_of_nonneg_right hsr (Real.sqrt_nonneg x)
    dsimp [Q] at hm
    nlinarith
  rw [budget_identity A x hxp.ne']
  apply (div_le_iff₀ hxp).mpr
  nlinarith

/-- The future height can be chosen before every disk, point and real part. -/
theorem eventually_scalar_guards (A : ℕ) (c C eps : ℝ)
    (hc : 0<c) (hC : 0≤C) (heps : 0<eps) :
    ∀ᶠ t : ℝ in atTop,
      64≤clock t ∧ step (clock t)<eps ∧
      (2:ℝ)^(A+1)*C≤c*(clock t)^3 ∧
      40*growth A (clock t)*step (clock t)/radius (clock t)≤1/4 := by
  filter_upwards [
    clock_tendsto.eventually (eventually_ge_atTop (64:ℝ)),
    clock_tendsto.eventually (eventually_ge_atTop (1+1/eps)),
    clock_tendsto.eventually (eventually_ge_atTop ((2:ℝ)^(A+1)*C/c)),
    clock_tendsto.eventually
      (eventually_ge_atTop ((30720*((A:ℝ)+2))^2))]
    with t hx he hCcut hb
  let x := clock t
  have hxp : 0<x := by dsimp [x]; linarith
  have hx1 : 1≤x := by dsimp [x]; linarith
  have hx9 : x≤x^9 := by
    simpa only [pow_one] using pow_le_pow_right₀ hx1 (by norm_num : 1≤9)
  have hh : step x<eps := by
    have hhx : 1/eps<x := by dsimp [x]; linarith
    have hi := (one_div_lt_one_div_of_lt (by positivity : 0<1/eps) hhx)
    have hi' : 1/x<eps := by simpa using hi
    exact (one_div_le_one_div_of_le hxp hx9).trans_lt hi'
  have hx3 : x≤x^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hx1 (by norm_num : 1≤3)
  have hcsmall : (2:ℝ)^(A+1)*C≤c*x^3 := by
    have ha : (2:ℝ)^(A+1)*C≤x*c := (div_le_iff₀ hc).mp hCcut
    nlinarith [mul_le_mul_of_nonneg_left hx3 hc.le]
  exact ⟨hx,hh,hcsmall,budget_of_square A x hb⟩

#print axioms eventually_scalar_guards
run_cmd do
  let targets : List Lean.Name := [
    ``clock_pos, ``clock_pow, ``clock_identities, ``clock_tendsto,
    ``pow_twelve_rpow, ``exp_growth, ``log_le_two_sqrt, ``scale_guards,
    ``budget_identity, ``budget_of_square, ``eventually_scalar_guards]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Item1ZeroFreeScaleClock
