import LogPhaseFirstDifference
import FlatDirichlet

/-!
Flat Dirichlet cancellation down to every nonzero low frequency.
The first-difference test and decreasing weights give 8/|u| in phase
units, or 16*pi/|t| in ordinary vertical frequency. The upper frequency
bound keeps increments away from nonzero integers.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace FlatLowFrequency

theorem weighted_bound (N M : ℕ) (a u σ : ℝ) (hN : 1 ≤ N) (hM : M ≤ N)
    (ha : (N : ℝ) ≤ a) (haUpper : a ≤ 2 * (N : ℝ))
    (hu : 0 < |u|) (huUpper : |u| ≤ (N : ℝ) / 4) (hσ : 1 ≤ σ) :
    ‖∑ n ∈ Finset.range M,
      Erdos374.KusminLandau151.e (LogPhaseShape.phase u (a + n)) *
        (((a + n) ^ (-σ) : ℝ) : ℂ)‖ ≤ 8 / |u| := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hw : ∀ n : ℕ, 0 ≤ (a + n) ^ (-σ) := by
    intro n
    apply Real.rpow_nonneg
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm : Antitone (fun n : ℕ => (a + n) ^ (-σ)) := by
    intro m n hmn
    exact Real.rpow_le_rpow_of_nonpos
      (by linarith [Nat.cast_nonneg (α := ℝ) m])
      (add_le_add (le_refl a) (Nat.cast_le.mpr hmn)) (by linarith)
  have hh := MonotoneWeight.antitone_weight_bound M
    (fun n => Erdos374.KusminLandau151.e (LogPhaseShape.phase u (a + n)))
    (fun n => (a + n) ^ (-σ)) (8 * (N : ℝ) / |u|) (by positivity) hw hm
    (fun m hm => LogPhaseFirstDifference.signed_bound N m a u hN (hm.trans hM)
      ha haUpper hu huUpper)
  have hw0 : a ^ (-σ) ≤ (N : ℝ)⁻¹ := by
    calc
      _ ≤ (N : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos hNp ha (by linarith)
      _ ≤ (N : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      _ = _ := Real.rpow_neg_one _
  simp only [Nat.cast_zero, add_zero] at hh
  apply hh.trans
  calc
    _ ≤ (8 * (N : ℝ) / |u|) * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hw0 (by positivity)
    _ = _ := by field_simp

theorem interval_bound (N lo hi : ℕ) (t σ : ℝ) (hN : 1 ≤ N)
    (hlo : N ≤ lo) (hhi : hi ≤ 2 * N)
    (ht : 0 < |t|) (htUpper : |t| ≤ (N : ℝ)) (hσ : 1 ≤ σ) :
    ‖Erdos374.HarmanGram152.verticalDirichlet152
      (Finset.Ioc lo hi) (fun _ => 1) σ t‖ ≤ (16 * Real.pi) / |t| := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have habs : |-t / (2 * Real.pi)| = |t| / (2 * Real.pi) := by
    rw [abs_div, abs_neg, abs_of_pos hpi]
  have hu : 0 < |-t / (2 * Real.pi)| := by rw [habs]; positivity
  have huUpper : |-t / (2 * Real.pi)| ≤ (N : ℝ) / 4 := by
    rw [habs]
    apply (div_le_iff₀ hpi).mpr
    have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [Real.pi_gt_three]
  by_cases hempty : hi ≤ lo
  · simp only [Erdos374.HarmanGram152.verticalDirichlet152,
      Finset.Ioc_eq_empty_of_le hempty, Finset.sum_empty, norm_zero]
    positivity
  · have hset : Finset.Ioc lo hi = Finset.Ico (lo + 1) (hi + 1) := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    unfold Erdos374.HarmanGram152.verticalDirichlet152
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_add_right, one_mul]
    have hh := weighted_bound N (hi - lo) ((lo : ℝ) + 1) (-t / (2 * Real.pi)) σ
      hN (by omega) (by exact_mod_cast (show N ≤ lo + 1 by omega))
      (by exact_mod_cast (show lo + 1 ≤ 2 * N by omega)) hu huUpper hσ
    have hright : 8 / |-t / (2 * Real.pi)| = (16 * Real.pi) / |t| := by
      rw [habs]
      field_simp
      ring
    rw [hright] at hh
    convert hh using 1
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [FlatDirichlet.vertical_term _ (by omega)]
    push_cast
    congr 2

end FlatLowFrequency

#print axioms FlatLowFrequency.interval_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``FlatLowFrequency.interval_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FLAT LOW FREQUENCY PASSED"
