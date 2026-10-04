import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! A vanishing scalar budget for normalized stopping losses. The polynomial
factor accounts for the actual profile mass and the dimension-one Euler ratio. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Set
open scoped Topology

namespace SieveStoppingBudget

def error (C s : ℝ) : ℝ :=
  2*C*exp 2*(1/s)^10*exp (-1/s)

theorem error_nonneg (C s : ℝ) (hC : 0 ≤ C) (hs : 0 < s) : 0 ≤ error C s := by
  unfold error
  positivity

theorem profile_exp_identity (s : ℝ) (hs : 0 < s) :
    exp (2*(2*log (1/s^2)+1)) = exp 2*(1/s)^8 := by
  rw [show 2*(2*log (1/s^2)+1) = 2+(4:ℕ)*log (1/s^2) by norm_num; ring,
    exp_add, exp_nat_mul, exp_log (by positivity)]
  congr 1
  field_simp

theorem tendsto_error_zero (C : ℝ) :
    Tendsto (error C) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => x^10*exp (-x)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 : ℝ) 1 (by norm_num)
  have hh := (ht.comp tendsto_inv_nhdsGT_zero).const_mul (2*C*exp 2)
  change Tendsto (fun s : ℝ => 2*C*exp 2*(1/s)^10*exp (-1/s)) _ _
  simpa only [Function.comp_def, one_div, neg_div, div_one, mul_zero,
    mul_assoc] using hh

theorem eventually_error_lt (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), error C s < ε :=
  (tendsto_order.mp (tendsto_error_zero C)).2 ε hε

theorem error_small (C ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ → error C s < ε := by
  obtain ⟨s₀, hs₀, hb⟩ := Metric.mem_nhdsWithin_iff.mp (eventually_error_lt C ε hε)
  refine ⟨s₀, hs₀, fun s hs hss => hb ⟨?_, hs⟩⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs] using hss

run_cmd do
  for decl in [``error_nonneg, ``profile_exp_identity, ``tendsto_error_zero,
    ``eventually_error_lt, ``error_small] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "NORMALIZED STOPPING SCALAR BUDGET TENDS TO ZERO"

end SieveStoppingBudget
end
