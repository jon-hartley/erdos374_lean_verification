import CheckedSamplingTypeIICancellation

/-!
Numerical coefficient windows for the Type II bound. This extends the
nearby-pair definitions in TypeIICancellation. The cutoff is constructed,
and the far-pair bounds are proved from common-scale hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CorrelationWindows
open TypeIICancellation

def nearCutoff (K : ℕ) (Q : ℝ) : ℕ := ⌊(K : ℝ) / Q⌋₊

theorem far_gap (K k l : ℕ) (Q : ℝ)
    (hfar : ¬nearby (nearCutoff K Q) k l) :
    (K : ℝ) / Q ≤ |(k : ℝ) - (l : ℝ)| := by
  have hfloor := Nat.lt_floor_add_one ((K : ℝ) / Q)
  change (K : ℝ) / Q < (nearCutoff K Q : ℝ) + 1 at hfloor
  simp only [nearby, not_and_or, not_le] at hfar
  rcases hfar with hk | hl
  · have hh : (l : ℝ) + (nearCutoff K Q : ℝ) + 1 ≤ k := by
      exact_mod_cast (show l + nearCutoff K Q + 1 ≤ k by omega)
    have hkl : (l : ℝ) ≤ k := by exact_mod_cast (show l ≤ k by omega)
    rw [abs_of_nonneg (sub_nonneg.mpr hkl)]
    linarith
  · have hh : (k : ℝ) + (nearCutoff K Q : ℝ) + 1 ≤ l := by
      exact_mod_cast (show k + nearCutoff K Q + 1 ≤ l by omega)
    have hkl : (k : ℝ) ≤ l := by exact_mod_cast (show k ≤ l by omega)
    rw [abs_of_nonpos (sub_nonpos.mpr hkl)]
    linarith

theorem nearby_budget (K : ℕ) (Q : ℝ) (hQ : 0 < Q) (hQK : Q ≤ K) :
    ((2 * nearCutoff K Q + 1 : ℕ) : ℝ) ≤ 3 * (K : ℝ) / Q := by
  have hf := Nat.floor_le (div_nonneg (Nat.cast_nonneg K) hQ.le)
  change (nearCutoff K Q : ℝ) ≤ (K : ℝ) / Q at hf
  have hratio : 1 ≤ (K : ℝ) / Q := (le_div_iff₀ hQ).mpr (by simpa using hQK)
  push_cast
  calc
    _ ≤ 2 * ((K : ℝ) / Q) + 1 := by linarith
    _ ≤ 3 * ((K : ℝ) / Q) := by linarith
    _ = _ := by ring

theorem reciprocal_sum_bounds (K k l : ℝ) (hK : 0 < K)
    (hk : K ≤ k) (hkUpper : k ≤ 2 * K)
    (hl : K ≤ l) (hlUpper : l ≤ 2 * K) :
    1 / K ≤ 1 / k + 1 / l ∧ 1 / k + 1 / l ≤ 2 / K := by
  have hkPos := hK.trans_le hk
  have hlPos := hK.trans_le hl
  constructor
  · have hkInv := one_div_le_one_div_of_le hkPos hkUpper
    have hlInv := one_div_le_one_div_of_le hlPos hlUpper
    have hid : 1 / K = 1 / (2 * K) + 1 / (2 * K) := by ring
    rw [hid]
    linarith
  · have hkInv := one_div_le_one_div_of_le hK hk
    have hlInv := one_div_le_one_div_of_le hK hl
    calc
      _ ≤ 1 / K + 1 / K := add_le_add hkInv hlInv
      _ = _ := by ring

theorem reciprocal_gap_bounds (K k l Q : ℝ) (hK : 0 < K) (hQ : 0 < Q)
    (hk : K ≤ k) (hkUpper : k ≤ 2 * K)
    (hl : K ≤ l) (hlUpper : l ≤ 2 * K)
    (hgap : K / Q ≤ |k - l|) :
    1 / (4 * K * Q) ≤ |1 / k - 1 / l| ∧
      |1 / k - 1 / l| ≤ 2 / K := by
  have hkPos := hK.trans_le hk
  have hlPos := hK.trans_le hl
  have hidentity : |1 / k - 1 / l| = |k - l| / (k * l) := by
    rw [show 1 / k - 1 / l = (l - k) / (k * l) by field_simp]
    rw [abs_div, abs_of_pos (mul_pos hkPos hlPos), abs_sub_comm]
  constructor
  · rw [hidentity]
    have hprod : k * l ≤ 4 * K ^ 2 := by nlinarith [mul_le_mul hkUpper hlUpper hlPos.le (by positivity : 0 ≤ 2 * K)]
    calc
      _ = (K / Q) / (4 * K ^ 2) := by field_simp
      _ ≤ |k - l| / (4 * K ^ 2) := div_le_div_of_nonneg_right hgap (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hprod
  · have htri : |1 / k - 1 / l| ≤ |1 / k| + |1 / l| := by
      simpa only [abs_neg, sub_eq_add_neg] using abs_add_le (1 / k) (-(1 / l))
    rw [abs_of_pos (by positivity : 0 < 1 / k),
      abs_of_pos (by positivity : 0 < 1 / l)] at htri
    exact htri.trans (reciprocal_sum_bounds K k l hK hk hkUpper hl hlUpper).2

theorem square_gap_bounds (K k l Q : ℝ) (hK : 0 < K) (hQ : 0 < Q)
    (hk : K ≤ k) (hkUpper : k ≤ 2 * K)
    (hl : K ≤ l) (hlUpper : l ≤ 2 * K)
    (hgap : K / Q ≤ |k - l|) :
    1 / (4 * K ^ 2 * Q) ≤ |1 / k ^ 2 - 1 / l ^ 2| ∧
      |1 / k ^ 2 - 1 / l ^ 2| ≤ 4 / K ^ 2 := by
  have hkPos := hK.trans_le hk
  have hlPos := hK.trans_le hl
  have hidentity : |1 / k ^ 2 - 1 / l ^ 2| =
      |1 / k - 1 / l| * (1 / k + 1 / l) := by
    rw [show 1 / k ^ 2 - 1 / l ^ 2 =
      (1 / k - 1 / l) * (1 / k + 1 / l) by ring]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / k + 1 / l)]
  rw [hidentity]
  have hg := reciprocal_gap_bounds K k l Q hK hQ hk hkUpper hl hlUpper hgap
  have hs := reciprocal_sum_bounds K k l hK hk hkUpper hl hlUpper
  constructor
  · calc
      _ = (1 / (4 * K * Q)) * (1 / K) := by ring
      _ ≤ _ := mul_le_mul hg.1 hs.1 (by positivity) (abs_nonneg _)
  · calc
      _ ≤ (2 / K) * (2 / K) := mul_le_mul hg.2 hs.2 (by positivity) (by positivity)
      _ = _ := by ring

theorem reciprocal_coefficient_window (r : ℕ) (D K k l Q L u v : ℝ)
    (hK : 0 < K) (hQ : 0 < Q) (hu : u ≠ 0)
    (hk : K ≤ k) (hkUpper : k ≤ 2 * K)
    (hl : K ≤ l) (hlUpper : l ≤ 2 * K)
    (hgap : K / Q ≤ |k - l|)
    (huLower : 4 * K * Q * D * L ≤ |u|)
    (huUpper : 2 * |u| ≤ K * D ^ r)
    (hdom : 4 * ((r + 3 : ℕ) : ℝ) * |v| ≤ |u| * D * K) :
    D * L ≤ |u * (1 / k - 1 / l)| ∧
      |u * (1 / k - 1 / l)| ≤ D ^ r ∧
      2 * ((r + 3 : ℕ) : ℝ) * (|v| / |u|) * (1 / k + 1 / l) ≤ D := by
  have hg := reciprocal_gap_bounds K k l Q hK hQ hk hkUpper hl hlUpper hgap
  have hs := reciprocal_sum_bounds K k l hK hk hkUpper hl hlUpper
  have huPos : 0 < |u| := abs_pos.mpr hu
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ |u| / (4 * K * Q) :=
        (le_div_iff₀ (by positivity)).mpr (by nlinarith only [huLower])
      _ = |u| * (1 / (4 * K * Q)) := by ring
      _ ≤ |u| * |1 / k - 1 / l| := mul_le_mul_of_nonneg_left hg.1 (abs_nonneg _)
      _ = _ := (abs_mul _ _).symm
  · rw [abs_mul]
    calc
      _ ≤ |u| * (2 / K) := mul_le_mul_of_nonneg_left hg.2 (abs_nonneg _)
      _ = (2 * |u|) / K := by ring
      _ ≤ _ := (div_le_iff₀ hK).mpr (by nlinarith only [huUpper])
  · calc
      _ ≤ 2 * ((r + 3 : ℕ) : ℝ) * (|v| / |u|) * (2 / K) :=
        mul_le_mul_of_nonneg_left hs.2 (by positivity)
      _ = (4 * ((r + 3 : ℕ) : ℝ) * |v|) / (|u| * K) := by ring
      _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hdom])

theorem square_coefficient_window (r : ℕ) (D K k l Q L v : ℝ)
    (hK : 0 < K) (hQ : 0 < Q)
    (hk : K ≤ k) (hkUpper : k ≤ 2 * K)
    (hl : K ≤ l) (hlUpper : l ≤ 2 * K)
    (hgap : K / Q ≤ |k - l|)
    (hvLower : 4 * K ^ 2 * Q * D ^ 2 * L ≤ |v|)
    (hvUpper : 4 * |v| ≤ K ^ 2 * D ^ (r + 1)) :
    D ^ 2 * L ≤ |v * (1 / k ^ 2 - 1 / l ^ 2)| ∧
      |v * (1 / k ^ 2 - 1 / l ^ 2)| ≤ D ^ (r + 1) := by
  have hg := square_gap_bounds K k l Q hK hQ hk hkUpper hl hlUpper hgap
  constructor
  · calc
      _ ≤ |v| / (4 * K ^ 2 * Q) :=
        (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hvLower])
      _ = |v| * (1 / (4 * K ^ 2 * Q)) := by ring
      _ ≤ |v| * |1 / k ^ 2 - 1 / l ^ 2| :=
        mul_le_mul_of_nonneg_left hg.1 (abs_nonneg _)
      _ = _ := (abs_mul _ _).symm
  · rw [abs_mul]
    calc
      _ ≤ |v| * (4 / K ^ 2) := mul_le_mul_of_nonneg_left hg.2 (abs_nonneg _)
      _ = (4 * |v|) / K ^ 2 := by ring
      _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hvUpper])

end CorrelationWindows

#print axioms CorrelationWindows.square_gap_bounds
#print axioms CorrelationWindows.reciprocal_coefficient_window
#print axioms CorrelationWindows.square_coefficient_window
run_cmd do
  for target in [``CorrelationWindows.far_gap, ``CorrelationWindows.nearby_budget,
      ``CorrelationWindows.square_gap_bounds,
      ``CorrelationWindows.reciprocal_coefficient_window,
      ``CorrelationWindows.square_coefficient_window] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "CORRELATION WINDOWS PASSED"

run_cmd do
  for target in [``CorrelationWindows.far_gap,
      ``CorrelationWindows.nearby_budget,
      ``CorrelationWindows.reciprocal_sum_bounds,
      ``CorrelationWindows.reciprocal_gap_bounds,
      ``CorrelationWindows.square_gap_bounds,
      ``CorrelationWindows.reciprocal_coefficient_window,
      ``CorrelationWindows.square_coefficient_window] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
