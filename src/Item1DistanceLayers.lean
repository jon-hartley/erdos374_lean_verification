import Item1LinearPhaseDistance

/-! A finite layer-count bound for reciprocal distance. A length of `N+1`
uses exactly `N` positive levels. Resonance, empty finite sets, and `N=0`
are included without floor functions. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace Item1DistanceLayers
open Item1LinearPhaseDistance

/-- A scalar finite layer bound, valid for every real cutoff. -/
theorem min_succ_le_levels (N : ℕ) (y : ℝ) :
    min ((N : ℝ) + 1) y ≤
      1 + ∑ k ∈ Finset.range N, if (k : ℝ) + 1 < y then (1 : ℝ) else 0 := by
  classical
  induction N with
  | zero =>
      simpa using min_le_left (1 : ℝ) y
  | succ N ih =>
      rw [Finset.sum_range_succ]
      by_cases h : (N : ℝ) + 1 < y
      · rw [if_pos h]
        rw [min_eq_left h.le] at ih
        have hleft := min_le_left (((N + 1 : ℕ) : ℝ) + 1) y
        push_cast at hleft ⊢
        linarith
      · rw [if_neg h]
        have hy : y ≤ (N : ℝ) + 1 := le_of_not_gt h
        have hy' : y ≤ ((N + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          linarith
        rw [min_eq_right hy', add_zero]
        simpa only [min_eq_right hy] using ih

/-- The strict reciprocal level condition, away from exact resonance. -/
theorem reciprocal_level_iff (k : ℕ) (d : ℝ) (hd : 0 < d) :
    (k : ℝ) + 1 < 1 / (2 * d) ↔ d < 1 / (2 * ((k : ℝ) + 1)) := by
  have hd2 : 0 < 2 * d := by positivity
  have hk2 : 0 < 2 * ((k : ℝ) + 1) := by positivity
  rw [lt_div_iff₀ hd2, lt_div_iff₀ hk2]
  constructor <;> intro h <;> nlinarith

/-- Exactly `N` near-integer levels bound a sum of length `N+1`. -/
theorem distanceBound_succ_le_levels (N : ℕ) (x : ℝ) :
    distanceBound (N + 1) x ≤
      1 + ∑ k ∈ Finset.range N,
        if integerDistance x < 1 / (2 * ((k : ℝ) + 1)) then (1 : ℝ) else 0 := by
  classical
  unfold distanceBound
  by_cases hz : integerDistance x = 0
  · rw [if_pos hz]
    have hp (k : ℕ) : 0 < 1 / (2 * ((k : ℝ) + 1)) := by positivity
    have hs : (∑ k ∈ Finset.range N,
        if integerDistance x < 1 / (2 * ((k : ℝ) + 1)) then (1 : ℝ) else 0) = N := by
      calc
        _ = ∑ _k ∈ Finset.range N, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hz, if_pos (hp k)]
        _ = (N : ℝ) := by simp
    rw [hs]
    push_cast
    linarith
  · rw [if_neg hz]
    have hd : 0 < integerDistance x :=
      lt_of_le_of_ne (integerDistance_nonneg x) (Ne.symm hz)
    have h := min_succ_le_levels N (1 / (2 * integerDistance x))
    simpa only [Nat.cast_add, Nat.cast_one, reciprocal_level_iff _ _ hd] using h

/-- The same bound indexed directly by a positive length. -/
theorem distanceBound_le_levels (L : ℕ) (hL : 1 ≤ L) (x : ℝ) :
    distanceBound L x ≤
      1 + ∑ k ∈ Finset.range (L - 1),
        if integerDistance x < 1 / (2 * ((k : ℝ) + 1)) then (1 : ℝ) else 0 := by
  simpa only [Nat.sub_add_cancel hL] using distanceBound_succ_le_levels (L - 1) x

/-- Summing the layer bound counts the points close to an integer at each level. -/
theorem sum_distanceBound_succ_le_level_counts {ι : Type*} (S : Finset ι)
    (N : ℕ) (x : ι → ℝ) :
    (∑ i ∈ S, distanceBound (N + 1) (x i)) ≤
      (S.card : ℝ) + ∑ k ∈ Finset.range N,
        ((S.filter (fun i => integerDistance (x i) <
          1 / (2 * ((k : ℝ) + 1)))).card : ℝ) := by
  classical
  calc
    (∑ i ∈ S, distanceBound (N + 1) (x i)) ≤
        ∑ i ∈ S, (1 + ∑ k ∈ Finset.range N,
          if integerDistance (x i) < 1 / (2 * ((k : ℝ) + 1)) then (1 : ℝ) else 0) :=
      Finset.sum_le_sum (fun i _ => distanceBound_succ_le_levels N (x i))
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_boole]

/-- The finite count form for an arbitrary positive length. -/
theorem sum_distanceBound_le_level_counts {ι : Type*} (S : Finset ι)
    (L : ℕ) (hL : 1 ≤ L) (x : ι → ℝ) :
    (∑ i ∈ S, distanceBound L (x i)) ≤
      (S.card : ℝ) + ∑ k ∈ Finset.range (L - 1),
        ((S.filter (fun i => integerDistance (x i) <
          1 / (2 * ((k : ℝ) + 1)))).card : ℝ) := by
  simpa only [Nat.sub_add_cancel hL] using
    sum_distanceBound_succ_le_level_counts S (L - 1) x

end Item1DistanceLayers

run_cmd do
  for target in [``Item1DistanceLayers.min_succ_le_levels,
      ``Item1DistanceLayers.reciprocal_level_iff,
      ``Item1DistanceLayers.distanceBound_succ_le_levels,
      ``Item1DistanceLayers.distanceBound_le_levels,
      ``Item1DistanceLayers.sum_distanceBound_succ_le_level_counts,
      ``Item1DistanceLayers.sum_distanceBound_le_level_counts] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "DISTANCE LAYERS: 6 standard-axiom theorem guards passed."
