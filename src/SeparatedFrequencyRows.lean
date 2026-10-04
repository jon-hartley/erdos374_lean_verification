import Erdos374_Update152

/-!
Reciprocal-distance rows for arbitrary real frequencies separated by one.
This extends the seed's integer-distance harmonic-sum argument by
injecting each one-sided row into the floors of its positive distances.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace SeparatedFrequencyRows

theorem positive_distance_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (d : α → ℝ) (T : ℝ)
    (hd : ∀ x ∈ s, 1 ≤ d x ∧ d x ≤ T)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ |d x - d y|) :
    (∑ x ∈ s, 1 / d x) ≤ (harmonic ⌈T⌉₊ : ℝ) := by
  have hfloor (x : α) (hx : x ∈ s) : 1 ≤ ⌊d x⌋₊ := by
    apply (Nat.le_floor_iff (by linarith [(hd x hx).1] : 0 ≤ d x)).mpr
    simpa only [Nat.cast_one] using (hd x hx).1
  have hinj : Set.InjOn (fun x => ⌊d x⌋₊) (s : Set α) := by
    intro x hx y hy heq
    change ⌊d x⌋₊ = ⌊d y⌋₊ at heq
    by_contra hne
    have hsepxy := hsep x hx y hy hne
    have hxlo := Nat.floor_le (by linarith [(hd x hx).1] : 0 ≤ d x)
    have hylo := Nat.floor_le (by linarith [(hd y hy).1] : 0 ≤ d y)
    have hxhi := Nat.lt_floor_add_one (d x)
    have hyhi := Nat.lt_floor_add_one (d y)
    rw [heq] at hxlo hxhi
    have hclose : |d x - d y| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  have himage : s.image (fun x => ⌊d x⌋₊) ⊆ Finset.Icc 1 ⌈T⌉₊ := by
    intro m hm
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
    refine Finset.mem_Icc.mpr ⟨hfloor x hx, ?_⟩
    have hle : (⌊d x⌋₊ : ℝ) ≤ (⌈T⌉₊ : ℕ) :=
      (Nat.floor_le (by linarith [(hd x hx).1])).trans
        ((hd x hx).2.trans (Nat.le_ceil T))
    exact_mod_cast hle
  calc
    _ ≤ ∑ x ∈ s, (⌊d x⌋₊ : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      rw [← one_div]
      apply one_div_le_one_div_of_le
        (by exact_mod_cast (show 0 < ⌊d x⌋₊ by have := hfloor x hx; omega))
        (Nat.floor_le (by linarith [(hd x hx).1]))
    _ = ∑ m ∈ s.image (fun x => ⌊d x⌋₊), (m : ℝ)⁻¹ := by
      rw [Finset.sum_image]
      exact fun x hx y hy hxy => hinj hx hy hxy
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌈T⌉₊, (m : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
    _ = _ := by simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem inverse_distance_row (r : Finset ℝ) (T t : ℝ) (ht : t ∈ r)
    (hsep : ∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|)
    (hdiam : ∀ x ∈ r, ∀ y ∈ r, |x - y| ≤ T) :
    (∑ u ∈ r.erase t, 1 / |t - u|) ≤ 2 * (harmonic ⌈T⌉₊ : ℝ) := by
  classical
  let lo := (r.erase t).filter (fun u => u < t)
  let hi := (r.erase t).filter (fun u => ¬ u < t)
  have hlo (u : ℝ) (hu : u ∈ lo) : u ∈ r ∧ u < t := by
    exact ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hu).1).2,
      (Finset.mem_filter.mp hu).2⟩
  have hhi (u : ℝ) (hu : u ∈ hi) : u ∈ r ∧ t < u := by
    have hh := Finset.mem_filter.mp hu
    exact ⟨(Finset.mem_erase.mp hh.1).2,
      lt_of_le_of_ne (le_of_not_gt hh.2) (Ne.symm (Finset.mem_erase.mp hh.1).1)⟩
  have hleft : (∑ u ∈ lo, 1 / |t - u|) ≤ (harmonic ⌈T⌉₊ : ℝ) := by
    have hh := positive_distance_sum lo (fun u => t - u) T (by
      intro u hu
      have hu' := hlo u hu
      simpa only [abs_of_pos (sub_pos.mpr hu'.2)] using
        And.intro (hsep t ht u hu'.1 (ne_of_gt hu'.2)) (hdiam t ht u hu'.1)) (by
      intro u hu v hv hne
      simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using
        hsep u (hlo u hu).1 v (hlo v hv).1 hne)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [abs_of_pos (sub_pos.mpr (hlo u hu).2)]
  have hright : (∑ u ∈ hi, 1 / |t - u|) ≤ (harmonic ⌈T⌉₊ : ℝ) := by
    have hh := positive_distance_sum hi (fun u => u - t) T (by
      intro u hu
      have hu' := hhi u hu
      simpa only [abs_of_pos (sub_pos.mpr hu'.2)] using
        And.intro (hsep u hu'.1 t ht (ne_of_gt hu'.2)) (hdiam u hu'.1 t ht)) (by
      intro u hu v hv hne
      simpa only [sub_sub_sub_cancel_right] using
        hsep u (hhi u hu).1 v (hhi v hv).1 hne)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr (hhi u hu).2)]
  have hsplit := Finset.sum_filter_add_sum_filter_not (r.erase t)
    (fun u => u < t) (fun u => 1 / |t - u|)
  change (∑ u ∈ lo, 1 / |t - u|) + (∑ u ∈ hi, 1 / |t - u|) = _ at hsplit
  linarith

end SeparatedFrequencyRows

#print axioms SeparatedFrequencyRows.inverse_distance_row
run_cmd do
  let axioms ← Lean.collectAxioms ``SeparatedFrequencyRows.inverse_distance_row
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "SEPARATED FREQUENCY ROWS PASSED"
