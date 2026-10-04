import Item1LinearPhaseDistance
import Item1NearIntegerCount

/-! Symmetry, resonance, and signed coefficients for the finite arithmetic sums. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace Item1SignedDistance
open Item1LinearPhaseDistance Item1NearIntegerCount

theorem integerDistance_neg (x : ℝ) : integerDistance (-x) = integerDistance x := by
  apply le_antisymm
  · have h := round_le (-x) (-round x)
    have he : |-x-((-round x:ℤ):ℝ)| = |x-(round x:ℝ)| := by
      rw [Int.cast_neg, show -x - -(round x:ℝ) = -(x-(round x:ℝ)) by ring, abs_neg]
    rw [he] at h
    exact h
  · have h := round_le x (-round (-x))
    have he : |x-((-round (-x):ℤ):ℝ)| = |-x-(round (-x):ℝ)| := by
      rw [Int.cast_neg, show x - -(round (-x):ℝ) = -(-x-(round (-x):ℝ)) by ring, abs_neg]
    rw [he] at h
    exact h

theorem integerDistance_mul_abs (x γ : ℝ) :
    integerDistance (x*|γ|) = integerDistance (x*γ) := by
  by_cases hγ : 0 ≤ γ
  · rw [abs_of_nonneg hγ]
  · rw [abs_of_neg (lt_of_not_ge hγ), mul_neg, integerDistance_neg]

theorem distanceBound_mul_abs (L : ℕ) (x γ : ℝ) :
    distanceBound L (x*|γ|) = distanceBound L (x*γ) := by
  simp only [distanceBound, integerDistance_mul_abs]

theorem distanceBound_zero (L : ℕ) : distanceBound L 0 = (L:ℝ) := by
  simp [distanceBound, integerDistance]

theorem distanceBound_le_length (L : ℕ) (x : ℝ) : distanceBound L x ≤ (L:ℝ) := by
  unfold distanceBound
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem nearIntegerSet_abs (D : ℕ) (γ δ : ℝ) :
    nearIntegerSet D |γ| δ = nearIntegerSet D γ δ := by
  classical
  ext m
  simp only [nearIntegerSet, Finset.mem_filter]
  change (_ ∧ integerDistance ((m:ℝ)*|γ|) < δ) ↔
    (_ ∧ integerDistance ((m:ℝ)*γ) < δ)
  rw [integerDistance_mul_abs]

theorem near_integer_count_signed (D : ℕ) (γ δ : ℝ) (hγ : γ ≠ 0) (hδ : 0 < δ) :
    ((nearIntegerSet D γ δ).card:ℝ) ≤
      4*(D:ℝ)*δ+2*(D:ℝ)*|γ|+4*δ/|γ|+2 := by
  rw [← nearIntegerSet_abs]
  exact near_integer_count D |γ| δ (abs_pos.mpr hγ) hδ

def arithmeticSum (L D : ℕ) (γ : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc (-(D:ℤ)) (D:ℤ), distanceBound L ((m:ℝ)*γ)

theorem arithmeticSum_nonneg (L D : ℕ) (γ : ℝ) : 0 ≤ arithmeticSum L D γ :=
  Finset.sum_nonneg (fun _ _ => distanceBound_nonneg _ _)

theorem arithmeticSum_abs (L D : ℕ) (γ : ℝ) : arithmeticSum L D |γ| = arithmeticSum L D γ := by
  unfold arithmeticSum
  apply Finset.sum_congr rfl
  intro m _
  exact distanceBound_mul_abs L (m:ℝ) γ

theorem symmetric_interval_card (D : ℕ) :
    ((Finset.Icc (-(D:ℤ)) (D:ℤ)).card:ℝ) = 2*(D:ℝ)+1 := by
  have h := Int.card_Icc_of_le (-(D:ℤ)) (D:ℤ) (by omega)
  have hc : ((Finset.Icc (-(D:ℤ)) (D:ℤ)).card:ℝ) =
      (D:ℝ)+1-(-(D:ℝ)) := by exact_mod_cast h
  linarith

theorem arithmeticSum_zero (L D : ℕ) : arithmeticSum L D 0 = (2*(D:ℝ)+1)*(L:ℝ) := by
  simp only [arithmeticSum, mul_zero, distanceBound_zero, Finset.sum_const, nsmul_eq_mul,
    symmetric_interval_card]

theorem arithmeticSum_le_trivial (L D : ℕ) (γ : ℝ) :
    arithmeticSum L D γ ≤ (2*(D:ℝ)+1)*(L:ℝ) := by
  calc
    arithmeticSum L D γ ≤ ∑ _m ∈ Finset.Icc (-(D:ℤ)) (D:ℤ), (L:ℝ) :=
      Finset.sum_le_sum (fun _ _ => distanceBound_le_length _ _)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, symmetric_interval_card]

end Item1SignedDistance

run_cmd do
  for target in [``Item1SignedDistance.integerDistance_neg,
      ``Item1SignedDistance.integerDistance_mul_abs,
      ``Item1SignedDistance.distanceBound_mul_abs,
      ``Item1SignedDistance.distanceBound_zero,
      ``Item1SignedDistance.distanceBound_le_length,
      ``Item1SignedDistance.nearIntegerSet_abs,
      ``Item1SignedDistance.near_integer_count_signed,
      ``Item1SignedDistance.arithmeticSum_nonneg,
      ``Item1SignedDistance.arithmeticSum_abs,
      ``Item1SignedDistance.symmetric_interval_card,
      ``Item1SignedDistance.arithmeticSum_zero,
      ``Item1SignedDistance.arithmeticSum_le_trivial] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "SIGNED DISTANCE: 12 standard-axiom theorem guards passed."
