import Item1PhasePerturbation
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Int.Interval

/-! Explicit finite geometric-sum bounds for unit complex phases.
The resonant case is separated so division by zero cannot create a false bound. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Item1LinearPhaseSum
open Item1PhasePerturbation

def phaseSum (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, unitPhase ((n:ℝ)*θ)

def phaseBound (N : ℕ) (θ : ℝ) : ℝ := by
  classical
  exact if unitPhase θ = 1 then (N:ℝ)
    else min (N:ℝ) (2/‖unitPhase θ-1‖)

theorem unitPhase_nat_mul (n : ℕ) (θ : ℝ) :
    unitPhase ((n:ℝ)*θ) = (unitPhase θ)^n := by
  induction n with
  | zero => simp [unitPhase]
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, unitPhase_add, ih, pow_succ]

theorem phaseSum_eq_geom_sum (N : ℕ) (θ : ℝ) :
    phaseSum N θ = ∑ n ∈ Finset.range N, (unitPhase θ)^n := by
  simp only [phaseSum, unitPhase_nat_mul]

theorem norm_geom_sum_le_length (q : ℂ) (hq : ‖q‖ = 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, q^n‖ ≤ (N:ℝ) := by
  simpa only [norm_pow, hq, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] using norm_sum_le (Finset.range N) (fun n => q^n)

/-- This product estimate remains valid when q=1. -/
theorem norm_geom_sum_mul_chord_le_two (q : ℂ) (hq : ‖q‖ = 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, q^n‖*‖q-1‖ ≤ 2 := by
  rw [← norm_mul, geom_sum_mul]
  calc
    ‖q^N-1‖ ≤ ‖q^N‖+‖(1:ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hq]

theorem norm_geom_sum_le_div_chord (q : ℂ) (hq : ‖q‖ = 1)
    (hne : q ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, q^n‖ ≤ 2/‖q-1‖ := by
  exact (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne))).mpr
    (norm_geom_sum_mul_chord_le_two q hq N)

theorem phaseBound_nonneg (N : ℕ) (θ : ℝ) : 0 ≤ phaseBound N θ := by
  classical
  unfold phaseBound
  split_ifs <;> positivity

theorem phaseBound_le_length (N : ℕ) (θ : ℝ) : phaseBound N θ ≤ (N:ℝ) := by
  classical
  unfold phaseBound
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem norm_phaseSum_le_bound (N : ℕ) (θ : ℝ) :
    ‖phaseSum N θ‖ ≤ phaseBound N θ := by
  classical
  rw [phaseSum_eq_geom_sum]
  unfold phaseBound
  split_ifs with h
  · exact norm_geom_sum_le_length _ (unitPhase_norm θ) N
  · exact le_min (norm_geom_sum_le_length _ (unitPhase_norm θ) N)
      (norm_geom_sum_le_div_chord _ (unitPhase_norm θ) h N)

/-- Coordinate intervals [0,N] contain N+1 integer points. -/
theorem norm_sum_Icc_zero_le_bound (N : ℕ) (θ : ℝ) :
    ‖∑ k ∈ Finset.Icc (0:ℤ) (N:ℤ), unitPhase (θ*(k:ℝ))‖ ≤
      phaseBound (N+1) θ := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  simpa [phaseSum, mul_comm] using norm_phaseSum_le_bound (N+1) θ

end Item1LinearPhaseSum

run_cmd do
  for target in [``Item1LinearPhaseSum.unitPhase_nat_mul,
      ``Item1LinearPhaseSum.phaseSum_eq_geom_sum,
      ``Item1LinearPhaseSum.norm_geom_sum_le_length,
      ``Item1LinearPhaseSum.norm_geom_sum_mul_chord_le_two,
      ``Item1LinearPhaseSum.norm_geom_sum_le_div_chord,
      ``Item1LinearPhaseSum.phaseBound_nonneg,
      ``Item1LinearPhaseSum.phaseBound_le_length,
      ``Item1LinearPhaseSum.norm_phaseSum_le_bound,
      ``Item1LinearPhaseSum.norm_sum_Icc_zero_le_bound] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "LINEAR PHASE SUM: 9 standard-axiom theorem guards passed."
