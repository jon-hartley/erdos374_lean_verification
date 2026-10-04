import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Exact rational contradiction for the three-mode zero detector.
These are scalar implications, not hidden zeta-growth or zero-free theorems.
The normalized symbols are x=q/h, u=h/R, v=M*h/R, a_k=h*Re F(s_k).
-/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Item1ZeroDetectionScalar

theorem margin_identity :
    (51/16:ℝ) - 80/21 + 21/80 + 1/4 = -23/210 := by norm_num

theorem normalized_detector_bound (x u v a0 a1 a2 : ℝ)
    (hx : 1 ≤ x) (hx1 : x ≤ 21/20)
    (hu : 0 ≤ u) (hu1 : u ≤ 1/8) (hv : 40*v ≤ 1/4)
    (ha0 : a0 ≤ 17/16)
    (ha1 : a1 ≤ 8*v-1/x+4*x*u^2)
    (ha2 : a2 ≤ 8*v) :
    3*a0+4*a1+a2 ≤ -23/210 := by
  have hxp : 0 < x := by linarith
  have hi : (80/21:ℝ) ≤ 4/x := by
    apply (le_div_iff₀ hxp).mpr
    nlinarith
  have hu2 : u^2 ≤ 1/64 := by nlinarith
  have hp : 16*x*u^2 ≤ 21/80 := by
    calc
      16*x*u^2 ≤ 16*x*(1/64) :=
        mul_le_mul_of_nonneg_left hu2 (by positivity)
      _ ≤ 21/80 := by nlinarith
  simp only [div_eq_mul_inv] at hi
  simp only [one_div] at ha1
  nlinarith

/-- Positivity and the detected aligned zero cannot both hold. -/
theorem normalized_detector_contradiction (x u v a0 a1 a2 : ℝ)
    (hx : 1 ≤ x) (hx1 : x ≤ 21/20)
    (hu : 0 ≤ u) (hu1 : u ≤ 1/8) (hv : 40*v ≤ 1/4)
    (ha0 : a0 ≤ 17/16)
    (ha1 : a1 ≤ 8*v-1/x+4*x*u^2)
    (ha2 : a2 ≤ 8*v)
    (hpos : 0 ≤ 3*a0+4*a1+a2) : False := by
  have hh := normalized_detector_bound x u v a0 a1 a2 hx hx1 hu hu1 hv ha0 ha1 ha2
  linarith

/-- Unnormalized form, retaining the complete q/r^2 root correction. -/
theorem local_detector_contradiction (h q R M f0 f1 f2 : ℝ)
    (hh : 0 < h) (hR : 0 < R) (hq : h ≤ q) (hq1 : q ≤ 21*h/20)
    (hr : 8*h ≤ R) (hbudget : 40*M*h/R ≤ 1/4)
    (hf0 : f0 ≤ 17/(16*h))
    (hf1 : f1 ≤ 8*M/R-1/q+4*q/R^2)
    (hf2 : f2 ≤ 8*M/R)
    (hpos : 0 ≤ 3*f0+4*f1+f2) : False := by
  have hqp : 0 < q := hh.trans_le hq
  have hx : 1 ≤ q/h := (le_div_iff₀ hh).mpr (by simpa using hq)
  have hx1 : q/h ≤ 21/20 := (div_le_iff₀ hh).mpr (by nlinarith)
  have hu : 0 ≤ h/R := (div_pos hh hR).le
  have hu1 : h/R ≤ 1/8 := (div_le_iff₀ hR).mpr (by nlinarith)
  have hv : 40*(M*h/R) ≤ 1/4 := by convert hbudget using 1 <;> ring
  have h0 : h*f0 ≤ 17/16 := by
    have hz := mul_le_mul_of_nonneg_left hf0 hh.le
    convert hz using 1 <;> field_simp [hh.ne'] <;> ring
  have h1 : h*f1 ≤ 8*(M*h/R)-1/(q/h)+4*(q/h)*(h/R)^2 := by
    have hz := mul_le_mul_of_nonneg_left hf1 hh.le
    convert hz using 1 <;> field_simp [hh.ne',hR.ne',hqp.ne'] <;> ring
  have h2 : h*f2 ≤ 8*(M*h/R) := by
    have hz := mul_le_mul_of_nonneg_left hf2 hh.le
    convert hz using 1 <;> ring
  have hp : 0 ≤ 3*(h*f0)+4*(h*f1)+h*f2 := by
    nlinarith [mul_nonneg hh.le hpos]
  exact normalized_detector_contradiction (q/h) (h/R) (M*h/R)
    (h*f0) (h*f1) (h*f2) hx hx1 hu hu1 hv h0 h1 h2 hp

/-- A zero at beta>=1-h/20 has the required aligned distance. -/
theorem candidate_distance (h β : ℝ) (hh : 0 < h)
    (hb : 1-h/20 ≤ β) (hb1 : β ≤ 1) :
    h ≤ 1+h-β ∧ 1+h-β ≤ 21*h/20 := by constructor <;> linarith

/-- Checks the constants in the ordinary 1/log-height specialization. -/
theorem classical_budget_identity (L : ℝ) (hL : L ≠ 0) :
    40*(3*L)*(1/(10000*L))/(1/4) = (6/125:ℝ) := by
  field_simp [hL]
  <;> ring

theorem classical_budget_margin : (6/125:ℝ) < 1/4 := by norm_num

theorem target_exponent_balance : (-3/4:ℝ)+(2/3) = -1/12 := by norm_num

theorem classical_width_coefficient : (1/10000:ℝ)/20=1/200000 := by norm_num

/-- A scalar identity only. The function-growth hypothesis in the report
is not proved by this calculation. -/
theorem growth_budget_identity (L A : ℝ) (hL : 0 < L) :
    40*((A+2)*Real.log L)*L^(-3/4:ℝ)/(1/(8*L^(2/3:ℝ))) =
      320*(A+2)*Real.log L*L^(-1/12:ℝ) := by
  have he : L^(-3/4:ℝ)*L^(2/3:ℝ) = L^(-1/12:ℝ) := by
    rw [←Real.rpow_add hL]
    norm_num
  calc
    _ = 320*(A+2)*Real.log L*(L^(-3/4:ℝ)*L^(2/3:ℝ)) := by
      simp only [div_eq_mul_inv, one_mul, inv_inv]
      ring
    _ = _ := by rw [he]

#print axioms local_detector_contradiction
run_cmd do
  let targets : List Lean.Name := [
    ``margin_identity, ``normalized_detector_bound, ``normalized_detector_contradiction,
    ``local_detector_contradiction, ``candidate_distance, ``classical_budget_identity,
    ``classical_budget_margin, ``target_exponent_balance, ``classical_width_coefficient,
    ``growth_budget_identity]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Item1ZeroDetectionScalar
