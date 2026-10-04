import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Algebraic budget for a WEAKER short-phase hypothesis.
This file proves no exponential-sum cancellation. Its sum-of-squares identity
explains precisely how much loss the final zeta-growth argument can tolerate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
namespace Item1WeakCubicBudget

theorem cubic_certificate (v : ℝ) :
    v^3-200*v+1200 =
      v*(v-8)^2+16*(v-33/4)^2+111 := by ring

theorem cubic_upper (v : ℝ) (hv : 0≤v) : v-v^3/200≤6 := by
  have hid := cubic_certificate v
  have hpos := mul_nonneg hv (sq_nonneg (v-8))
  nlinarith [sq_nonneg (v-33/4)]

/-- A scaled polynomial inequality, with all divisibility/positivity guards.
x = (log t)^(1/3), y = log log t in the application. -/
theorem cubic_exponent (x y u Delta : ℝ) (hx : 0<x) (hy : 0<y)
    (hu : 0≤u) (hD : Delta≤1/x^2) :
    Delta*u-u^3/(200*x^6*y^2) ≤ 6*y := by
  let v := u/(x^2*y)
  have hv : 0≤v := by dsimp [v]; positivity
  have hc := mul_le_mul_of_nonneg_left (cubic_upper v hv) hy.le
  have hid : u/x^2-u^3/(200*x^6*y^2)=y*(v-v^3/200) := by
    dsimp [v]
    field_simp
  have hDu := mul_le_mul_of_nonneg_right hD hu
  have hDu' : Delta*u≤u/x^2 := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hDu
  have hh : Delta*u-u^3/(200*x^6*y^2) ≤
      u/x^2-u^3/(200*x^6*y^2) := sub_le_sub_right hDu' _
  rw [←hid] at hc
  nlinarith only [hh, hc]

theorem cube_root_ids (L : ℝ) (hL : 0<L) :
    (L^(1/3:ℝ))^2=L^(2/3:ℝ) ∧
    (L^(1/3:ℝ))^6=L^2 := by
  constructor
  · rw [←Real.rpow_mul_natCast hL.le (1/3:ℝ) 2]
    norm_num
  · rw [←Real.rpow_mul_natCast hL.le (1/3:ℝ) 6]
    norm_num

theorem logarithmic_cubic_exponent (L u Delta : ℝ) (hL : 1<L)
    (hu : 0≤u) (hD : Delta≤1/L^(2/3:ℝ)) :
    Delta*u-u^3/(200*L^2*(Real.log L)^2)≤6*Real.log L := by
  have hp : 0<L := by linarith
  obtain ⟨hi2,hi6⟩ := cube_root_ids L hp
  have hh := cubic_exponent (L^(1/3:ℝ)) (Real.log L) u Delta
    (Real.rpow_pos_of_pos hp _) (Real.log_pos hL) hu (by rw [hi2]; exact hD)
  simpa only [hi6] using hh

theorem exponential_cubic_envelope (L u Delta : ℝ) (hL : 1<L)
    (hu : 0≤u) (hD : Delta≤1/L^(2/3:ℝ)) :
    Real.exp (Delta*u-u^3/(200*L^2*(Real.log L)^2))≤L^6 := by
  have hh := Real.exp_le_exp.mpr (logarithmic_cubic_exponent L u Delta hL hu hD)
  have he : Real.exp (6*Real.log L)=L^6 := by
    rw [←show Real.log (L^6)=6*Real.log L by exact Real.log_pow L 6,
      Real.exp_log (pow_pos (by linarith) 6)]
  simpa [he] using hh

/-- The count is the number of dyadic blocks, not a fixed geometric host count. -/
theorem block_sum_budget {ι : Type*} (s : Finset ι) (b : ι → ℝ) (L : ℝ)
    (hL : 0≤L) (hc : (s.card:ℝ)≤5*L) (hb : ∀ j∈s, b j≤16*L^6) :
    (∑ j∈s, b j)≤80*L^7 := by
  have hcoef : 0≤16*L^6 := mul_nonneg (by norm_num) (pow_nonneg hL _)
  calc
    _ ≤ ∑ _j∈s, 16*L^6 := Finset.sum_le_sum hb
    _ = (s.card:ℝ)*(16*L^6) := by simp
    _ ≤ (5*L)*(16*L^6) := mul_le_mul_of_nonneg_right hc hcoef
    _ = 80*L^7 := by ring

theorem final_growth_budget (Z S L : ℝ) (hL : 1≤L)
    (hZ : Z≤S+8) (hS : S≤80*L^7) : Z≤128*L^7 := by
  have hp : 1≤L^7 := one_le_pow₀ hL
  nlinarith

/-- A safe Euler-tail bound once the finite cutoff is at least t^2.
q and p are Q^(1-sigma) and Q^(-sigma); their scalar bounds are explicit. -/
theorem euler_tail_budget (t sigma q p : ℝ) (ht : 1≤t)
    (hs : 1/2≤sigma) (hq : q≤t) (hp0 : 0≤p) (hp : p≤1/t) :
    q/t+(3/2)*p+2*t*p/sigma≤8 := by
  have htp : 0<t := by linarith
  have hsp : 0<sigma := by linarith
  have hqt : q/t≤1 := (div_le_one htp).mpr hq
  have hpt : t*p≤1 := by
    have hh := (le_div_iff₀ htp).mp hp
    nlinarith [mul_nonneg htp.le hp0]
  have hp1 : p≤1 := by
    have hh : 1/t≤1 := (div_le_one htp).mpr ht
    exact hp.trans hh
  have hr : 2*t*p/sigma≤4 := by
    apply (div_le_iff₀ hsp).mpr
    nlinarith
  linarith

end Item1WeakCubicBudget

run_cmd do
  for target in [``Item1WeakCubicBudget.cubic_certificate, ``Item1WeakCubicBudget.cubic_upper,
    ``Item1WeakCubicBudget.cubic_exponent, ``Item1WeakCubicBudget.cube_root_ids,
    ``Item1WeakCubicBudget.logarithmic_cubic_exponent,
    ``Item1WeakCubicBudget.exponential_cubic_envelope,
    ``Item1WeakCubicBudget.block_sum_budget, ``Item1WeakCubicBudget.final_growth_budget,
    ``Item1WeakCubicBudget.euler_tail_budget] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1WeakCubicBudget.exponential_cubic_envelope
#print axioms Item1WeakCubicBudget.euler_tail_budget
