import FrequencyBlocks

/-!
A finite separated-point count controls Lebesgue outer measure. A
maximal finite set covers the original set by intervals of radius one.
No measurability assumption on the original set is needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace SeparatedSetMeasure

theorem volume_bound (S : Set ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ r : Finset ℝ, (↑r : Set ℝ) ⊆ S →
      (∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|) → (r.card : ℝ) ≤ C) :
    volume S ≤ ENNReal.ofReal (2 * C) := by
  classical
  let P : ℕ → Prop := fun n => ∃ r : Finset ℝ, r.card = n ∧
    (↑r : Set ℝ) ⊆ S ∧ ∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|
  have hzero : P 0 := ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨r, hrCard, hrS, hrSep⟩ :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le ⌊C⌋₊) hzero
  have hmax (q : Finset ℝ) (hqS : (↑q : Set ℝ) ⊆ S)
      (hqSep : ∀ x ∈ q, ∀ y ∈ q, x ≠ y → 1 ≤ |x - y|) : q.card ≤ r.card := by
    have hqFloor : q.card ≤ ⌊C⌋₊ := (Nat.le_floor_iff hC).mpr (hcount q hqS hqSep)
    rw [hrCard]
    exact Nat.le_findGreatest hqFloor (show P q.card from ⟨q, rfl, hqS, hqSep⟩)
  have hcover : S ⊆ ⋃ t ∈ r, Icc (t - 1) (t + 1) := by
    intro x hx
    by_contra hnot
    have hfar : ∀ t ∈ r, 1 < |x - t| := by
      intro t ht
      by_contra hclose
      have hh := abs_le.mp (le_of_not_gt hclose)
      exact hnot (mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, ⟨by linarith, by linarith⟩⟩⟩)
    have hxnot : x ∉ r := by
      intro hxr
      have hh := hfar x hxr
      norm_num at hh
    have hsep : ∀ y ∈ insert x r, ∀ z ∈ insert x r, y ≠ z → 1 ≤ |y - z| := by
      intro y hy z hz hne
      rcases Finset.mem_insert.mp hy with hyEq | hyr
      · subst y
        rcases Finset.mem_insert.mp hz with hzEq | hzr
        · exact (hne hzEq.symm).elim
        · exact (hfar z hzr).le
      · rcases Finset.mem_insert.mp hz with hzEq | hzr
        · subst z
          simpa only [abs_sub_comm] using (hfar y hyr).le
        · exact hrSep y hyr z hzr hne
    have hlarge := hmax (insert x r) (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hrS hy) hsep
    rw [Finset.card_insert_of_notMem hxnot] at hlarge
    omega
  calc
    volume S ≤ volume (⋃ t ∈ r, Icc (t - 1) (t + 1)) := measure_mono hcover
    _ ≤ ∑ t ∈ r, volume (Icc (t - 1) (t + 1)) := measure_biUnion_finset_le _ _
    _ = (r.card : ℝ≥0∞) * 2 := by
      simp only [Real.volume_Icc, show ∀ t : ℝ, t + 1 - (t - 1) = 2 by intro t; ring,
        ENNReal.ofReal_ofNat, Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal (2 * (r.card : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
      ring
    _ ≤ ENNReal.ofReal (2 * C) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hcount r hrS hrSep) (by norm_num))

theorem real_volume_bound (S : Set ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ r : Finset ℝ, (↑r : Set ℝ) ⊆ S →
      (∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|) → (r.card : ℝ) ≤ C) :
    volume.real S ≤ 2 * C := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (volume_bound S C hC hcount)
  simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * C)] using hh

end SeparatedSetMeasure

#print axioms SeparatedSetMeasure.real_volume_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``SeparatedSetMeasure.real_volume_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "SEPARATED SET MEASURE PASSED"
