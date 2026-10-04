import Item1SignedDistance
import Item1DistanceLayers
import Item1HarmonicBound

/-! Explicit logarithmic estimates for the finite arithmetic factors.
The zero-coefficient branch retains the exact full interval contribution. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace Item1ArithmeticLogBound
open Item1LinearPhaseDistance Item1NearIntegerCount Item1SignedDistance
open Item1DistanceLayers Item1HarmonicBound

theorem near_integer_level_count (D k : ℕ) (γ : ℝ) (hγ : γ ≠ 0) :
    ((nearIntegerSet D γ (1/(2*((k:ℝ)+1)))).card:ℝ) ≤
      (2*(D:ℝ)*|γ|+2)+2*((D:ℝ)+1/|γ|)*(1/((k:ℝ)+1)) := by
  have h := near_integer_count_signed D γ (1/(2*((k:ℝ)+1))) hγ (by positivity)
  have hk : (k:ℝ)+1 ≠ 0 := ne_of_gt (by positivity)
  have hg : |γ| ≠ 0 := abs_ne_zero.mpr hγ
  convert h using 1 <;> field_simp [hk, hg] <;> ring

/-- Summing the exact finite levels gives an explicit harmonic factor. -/
theorem arithmeticSum_succ_le_harmonic (N D : ℕ) (γ : ℝ) (hγ : γ ≠ 0) :
    arithmeticSum (N+1) D γ ≤
      (2*(D:ℝ)+1)+(N:ℝ)*(2*(D:ℝ)*|γ|+2)+
        2*((D:ℝ)+1/|γ|)*(∑ k ∈ Finset.range N, 1/((k:ℝ)+1)) := by
  have h := sum_distanceBound_succ_le_level_counts
    (Finset.Icc (-(D:ℤ)) (D:ℤ)) N (fun m : ℤ => (m:ℝ)*γ)
  change arithmeticSum (N+1) D γ ≤ _ at h
  rw [symmetric_interval_card] at h
  have hcounts :
      (∑ k ∈ Finset.range N,
        (((Finset.Icc (-(D:ℤ)) (D:ℤ)).filter
          (fun m : ℤ => integerDistance ((m:ℝ)*γ) < 1/(2*((k:ℝ)+1)))).card:ℝ)) ≤
      (∑ k ∈ Finset.range N,
        ((2*(D:ℝ)*|γ|+2)+2*((D:ℝ)+1/|γ|)*(1/((k:ℝ)+1)))) := by
    apply Finset.sum_le_sum
    intro k _
    exact near_integer_level_count D k γ hγ
  calc
    arithmeticSum (N+1) D γ ≤
        (2*(D:ℝ)+1)+∑ k ∈ Finset.range N,
          ((2*(D:ℝ)*|γ|+2)+2*((D:ℝ)+1/|γ|)*(1/((k:ℝ)+1))) :=
      h.trans (add_le_add le_rfl hcounts)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum]
      ring

def logMajorant (N D : ℕ) (γ : ℝ) : ℝ :=
  (2*(D:ℝ)+1)+(N:ℝ)*(2*(D:ℝ)*|γ|+2)+
    2*((D:ℝ)+1/|γ|)*(1+Real.log ((N:ℝ)+1))

theorem logMajorant_nonneg (N D : ℕ) (γ : ℝ) : 0 ≤ logMajorant N D γ := by
  have hl : 0 ≤ Real.log ((N:ℝ)+1) :=
    Real.log_nonneg (by have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg N; linarith)
  unfold logMajorant
  positivity

/-- All constants and the logarithmic loss are explicit. -/
theorem arithmeticSum_succ_le_log (N D : ℕ) (γ : ℝ) (hγ : γ ≠ 0) :
    arithmeticSum (N+1) D γ ≤ logMajorant N D γ := by
  apply (arithmeticSum_succ_le_harmonic N D γ hγ).trans
  unfold logMajorant
  have hc : 0 ≤ 2*((D:ℝ)+1/|γ|) := by positivity
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (sum_range_reciprocal_le_log_succ N) hc)

/-- Retain the trivial cap, and treat the zero coefficient separately. -/
def arithmeticBound (N D : ℕ) (γ : ℝ) : ℝ :=
  if γ = 0 then (2*(D:ℝ)+1)*((N:ℝ)+1)
  else min ((2*(D:ℝ)+1)*((N:ℝ)+1)) (logMajorant N D γ)

theorem arithmeticBound_nonneg (N D : ℕ) (γ : ℝ) : 0 ≤ arithmeticBound N D γ := by
  unfold arithmeticBound
  split_ifs
  · positivity
  · exact le_min (by positivity) (logMajorant_nonneg N D γ)

theorem arithmeticBound_le_trivial (N D : ℕ) (γ : ℝ) :
    arithmeticBound N D γ ≤ (2*(D:ℝ)+1)*((N:ℝ)+1) := by
  unfold arithmeticBound
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem arithmeticSum_succ_le_bound (N D : ℕ) (γ : ℝ) :
    arithmeticSum (N+1) D γ ≤ arithmeticBound N D γ := by
  unfold arithmeticBound
  split_ifs with hγ
  · subst γ
    simpa only [Nat.cast_add, Nat.cast_one] using (arithmeticSum_zero (N+1) D).le
  · exact le_min (by simpa only [Nat.cast_add, Nat.cast_one] using
      arithmeticSum_le_trivial (N+1) D γ) (arithmeticSum_succ_le_log N D γ hγ)

end Item1ArithmeticLogBound

run_cmd do
  for target in [``Item1ArithmeticLogBound.near_integer_level_count,
      ``Item1ArithmeticLogBound.arithmeticSum_succ_le_harmonic,
      ``Item1ArithmeticLogBound.logMajorant_nonneg,
      ``Item1ArithmeticLogBound.arithmeticSum_succ_le_log,
      ``Item1ArithmeticLogBound.arithmeticBound_nonneg,
      ``Item1ArithmeticLogBound.arithmeticBound_le_trivial,
      ``Item1ArithmeticLogBound.arithmeticSum_succ_le_bound] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "ARITHMETIC LOG BOUND: 7 standard-axiom theorem guards passed."
