import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! Absolute and normalized scalar collision budgets. The normalized budget
charges the Euler ratio as well; attaching actual arithmetic estimates is
a separate theorem. The absolute budget alone does not control that ratio. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace SieveCollisionDecay

def error (s : ℝ) : ℝ :=
  5 * s^9 * (4 * Real.log (1/s^2) + 1) * Real.exp (17/16) *
    (1/s^2 : ℝ)^(17/4 : ℝ)

/-- The budget after combining the constant-2 prime mass estimate with both
the ordered-profile factor and the Euler-product ratio factor. -/
def normalizedError (s : ℝ) : ℝ :=
  3 * s^9 * (2 * Real.log (1/s^2) + 1) * Real.exp (17/8) *
    (1/s^2 : ℝ)^(17/4 : ℝ)

theorem reciprocal_power_balance (s : ℝ) (hs : 0 < s) :
    s^9 * (1/s^2 : ℝ)^(17/4 : ℝ) = s^(1/2 : ℝ) := by
  rw [one_div, Real.inv_rpow (sq_nonneg s), ← Real.rpow_neg (sq_nonneg s)]
  rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le,
    ← Real.rpow_natCast s 9, ← Real.rpow_add hs]
  norm_num

theorem log_reciprocal_square (s : ℝ) :
    Real.log (1/s^2) = 2 * Real.log (1/s) := by
  rw [one_div, Real.log_inv, Real.log_pow, one_div, Real.log_inv]
  ring

theorem error_eq (s : ℝ) (hs : 0 < s) :
    error s = 5 * Real.exp (17/16) * s^(1/2 : ℝ) *
      (8 * Real.log (1/s) + 1) := by
  unfold error
  rw [log_reciprocal_square]
  calc
    _ = 5 * Real.exp (17/16) * (s^9 * (1/s^2 : ℝ)^(17/4 : ℝ)) *
        (8 * Real.log (1/s) + 1) := by ring
    _ = _ := by rw [reciprocal_power_balance s hs]

theorem normalizedError_eq (s : ℝ) (hs : 0 < s) :
    normalizedError s = 3 * Real.exp (17/8) * s^(1/2 : ℝ) *
      (4 * Real.log (1/s) + 1) := by
  unfold normalizedError
  rw [log_reciprocal_square]
  calc
    _ = 3 * Real.exp (17/8) * (s^9 * (1/s^2 : ℝ)^(17/4 : ℝ)) *
        (4 * Real.log (1/s) + 1) := by ring
    _ = _ := by rw [reciprocal_power_balance s hs]

theorem error_nonneg (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) : 0 ≤ error s := by
  rw [error_eq s hs]
  have hl : 0 ≤ Real.log (1/s) := Real.log_nonneg
    ((one_le_div hs).mpr hs1)
  positivity

theorem normal_form_tendsto_zero (a b c : ℝ) :
    Tendsto (fun s : ℝ => a * Real.exp c * s^(1/2 : ℝ) *
      (b * Real.log (1/s) + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hp : Tendsto (fun s : ℝ => s^(1/2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1/2)).tendsto 0).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hl := tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1/2)
  have h := ((hl.neg.const_mul b).add hp).const_mul (a * Real.exp c)
  simp only [neg_zero, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [] with s
  simp only [one_div, Real.log_inv]
  ring

theorem tendsto_error_zero : Tendsto error (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply (normal_form_tendsto_zero 5 8 (17/16)).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (error_eq s hs).symm

theorem tendsto_normalizedError_zero :
    Tendsto normalizedError (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply (normal_form_tendsto_zero 3 4 (17/8)).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (normalizedError_eq s hs).symm

theorem eventually_error_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), error s < ε :=
  (tendsto_order.mp tendsto_error_zero).2 ε hε

theorem eventually_normalizedError_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), normalizedError s < ε :=
  (tendsto_order.mp tendsto_normalizedError_zero).2 ε hε

theorem normalizedError_small (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ → normalizedError s < ε := by
  obtain ⟨s₀, hs₀, hb⟩ := Metric.mem_nhdsWithin_iff.mp
    (eventually_normalizedError_lt ε hε)
  refine ⟨s₀, hs₀, fun s hs hss => hb ⟨?_, hs⟩⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs] using hss

#print axioms tendsto_error_zero
run_cmd do
  for decl in [``reciprocal_power_balance, ``log_reciprocal_square, ``error_eq,
      ``normalizedError_eq, ``error_nonneg, ``normal_form_tendsto_zero,
      ``tendsto_error_zero, ``tendsto_normalizedError_zero, ``eventually_error_lt,
      ``eventually_normalizedError_lt, ``normalizedError_small] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SIEVE COLLISION DECAY PASSED; standard axioms only"

end SieveCollisionDecay
end
