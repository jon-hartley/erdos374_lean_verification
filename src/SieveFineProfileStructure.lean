import SieveProfileTransition
import SieveProfileStaircase
import SieveProfileSupersolution
import SieveUpperProfileLinear

/-! Endpoint-safe fine-grid structure and the finite threshold intersection.
Numeric row bounds are explicit inputs here and must be discharged by a
separate actual-prime certificate adapter. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Filter
open scoped BigOperators
namespace SieveFineProfileStructure
open SieveStoppingTwoStep

def rowPoint (i : ℕ) : ℝ := 2+(i:ℝ)/40
def cut (i : ℕ) : ℝ := 2+((i:ℝ)+1)/40
def coefficient (v : ℕ → ℝ) (i : ℕ) : ℝ := v i-v (i+1)
def profile (v : ℕ → ℝ) (r : ℝ) : ℝ :=
  SieveProfileTransition.profile (Finset.range 720) (coefficient v) cut r

theorem cut_ge_two (i : ℕ) : 2 ≤ cut i := by
  unfold cut
  have hi : 0 ≤ (i:ℝ) := Nat.cast_nonneg i
  linarith

theorem grid_cover (r : ℝ) (hr : 2 ≤ r) (hR : r < 20) :
    ∃ i : ℕ, i < 720 ∧ rowPoint i ≤ r ∧ r ≤ cut i := by
  let i := ⌊40*(r-2)⌋₊
  have h0 : 0 ≤ 40*(r-2) := by linarith
  have hlo : (i:ℝ) ≤ 40*(r-2) := Nat.floor_le h0
  have hhi : 40*(r-2) < (i:ℝ)+1 := Nat.lt_floor_add_one _
  refine ⟨i, ?_, ?_, ?_⟩
  · have : (i:ℝ) < 720 := by linarith
    exact_mod_cast this
  · unfold rowPoint
    linarith
  · unfold cut
    linarith

theorem profile_nonneg (v : ℕ → ℝ) (hd : ∀ j < 720, 0 ≤ coefficient v j)
    (r : ℝ) : 0 ≤ profile v r :=
  SieveProfileTransition.profile_nonneg _ _ _ (fun j hj => hd j (Finset.mem_range.mp hj)) r

theorem profile_tail (v : ℕ → ℝ) (hd : ∀ j < 720, 0 ≤ coefficient v j)
    (r : ℝ) (hr : 20 ≤ r) : 91*exp (-r) ≤ profile v r :=
  SieveProfileTransition.profile_tail_lower _ _ _
    (fun j hj => hd j (Finset.mem_range.mp hj)) r hr

theorem profile_lower (v : ℕ → ℝ) (hd : ∀ j < 720, 0 ≤ coefficient v j)
    (hN : v 720 = 0) (i : ℕ) (hi : i ≤ 720) (r : ℝ) (hr : r ≤ cut i) :
    v i ≤ profile v r := by
  have hsum : v i ≤ SieveProfileTransition.staircase (Finset.range 720) (coefficient v) cut r := by
    have hs := SieveProfileStaircase.suffix_sum 720 i v hi
    rw [hN, sub_zero] at hs
    rw [← hs]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hij : i ≤ j
    · have hc : cut i ≤ cut j := by
        have hijR : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
        unfold cut
        linarith
      simp only [hij, ite_true, hr.trans hc, mul_one, coefficient, le_refl]
    · simp only [hij, ite_false]
      exact mul_nonneg (hd j (Finset.mem_range.mp hj)) (by split_ifs <;> norm_num)
  exact hsum.trans (le_add_of_nonneg_right (SieveProfileExponentialTail.tail_nonneg r))

theorem postfixed_of_rows (v : ℕ → ℝ)
    (hd : ∀ j < 720, 0 ≤ coefficient v j) (hN : v 720 = 0)
    (hrows : ∀ i < 720, ∃ B : ℝ, 2 ≤ B ∧ ∀ z T : ℝ,
      B ≤ z → z^2 ≤ T → rowPoint i ≤ log T/log z →
      forcing T z+operator (fun T z => profile v (log T/log z)) T z ≤ v i) :
    SieveProfileSupersolution.Postfixed (profile v) := by
  have he : ∀ᶠ z : ℝ in atTop, ∀ i ∈ Finset.range 720, ∀ T : ℝ,
      z^2 ≤ T → rowPoint i ≤ log T/log z →
      forcing T z+operator (fun T z => profile v (log T/log z)) T z ≤ v i := by
    apply (eventually_all_finset (Finset.range 720)).mpr
    intro i hi
    obtain ⟨B, _hB, hb⟩ := hrows i (Finset.mem_range.mp hi)
    filter_upwards [eventually_ge_atTop B] with z hz
    exact fun T hT hr => hb z T hz hT hr
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp he
  refine ⟨max 2 B₀, le_max_left _ _, ?_⟩
  intro z T hz hT hr20
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hz
  have hr2 := SieveStoppingArithmeticContraction.parameter_ge_two T z hz2 hT
  obtain ⟨i, hi, hl, hu⟩ := grid_cover _ hr2 hr20
  exact (hB₀ z ((le_max_right _ _).trans hz) i (Finset.mem_range.mpr hi) T hT hl).trans
    (profile_lower v hd hN i (by omega) _ hu)

theorem weighted_differences (N : ℕ) (v : ℕ → ℝ) :
    (∑ j ∈ Finset.range N, (v j-v (j+1))*((j:ℝ)+1)) =
      (∑ j ∈ Finset.range N, v j)-(N:ℝ)*v N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    push_cast
    ring

theorem area_eq (v : ℕ → ℝ) (hN : v 720 = 0) :
    SieveUpperProfileLinear.area (Finset.range 720) (coefficient v) cut =
      (∑ j ∈ Finset.range 720, v j)/40 := by
  unfold SieveUpperProfileLinear.area coefficient cut
  have he : (∑ j ∈ Finset.range 720, (v j-v (j+1))*
      ((2+((j:ℝ)+1)/40)-2)) =
      (∑ j ∈ Finset.range 720, (v j-v (j+1))*((j:ℝ)+1))/40 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he, weighted_differences, hN, mul_zero, sub_zero]

run_cmd do
  for decl in [``cut_ge_two, ``grid_cover, ``profile_nonneg, ``profile_tail,
      ``profile_lower, ``postfixed_of_rows, ``weighted_differences, ``area_eq] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FINE GRID STRUCTURE AND UNIFORM ROW INTERSECTION CHECKED"
end SieveFineProfileStructure
end
