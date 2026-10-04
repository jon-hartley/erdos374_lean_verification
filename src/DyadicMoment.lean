import DirichletLargeValueMeasure

/-!
A finite amplitude decomposition for moments of order at least two.
The upper dyadic cover is explicit. This keeps both the small-value
mean square and every large-value level measure visible.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace DyadicMoment
open DirichletLargeValueMeasure

theorem exists_band (J : ℕ) (v x : ℝ) (hvx : v < x)
    (hx : x ≤ (2 : ℝ) ^ J * v) :
    ∃ j ∈ Finset.range J, (2 : ℝ) ^ j * v < x ∧ x ≤ (2 : ℝ) ^ (j + 1) * v := by
  induction J with
  | zero => simp only [pow_zero, one_mul] at hx; linarith
  | succ J ih =>
    by_cases hsmall : x ≤ (2 : ℝ) ^ J * v
    · obtain ⟨j, hj, hl, hu⟩ := ih hsmall
      exact ⟨j, Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega), hl, hu⟩
    · exact ⟨J, Finset.mem_range.mpr (by omega), lt_of_not_ge hsmall, hx⟩

theorem small_value_bound (x v p : ℝ) (hx : 0 ≤ x) (hxv : x ≤ v) (hp : 2 ≤ p) :
    x ^ p ≤ v ^ (p - 2) * x ^ 2 := by
  have heq : x ^ p = x ^ (p - 2) * x ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add_of_nonneg hx (by linarith) (by norm_num)]
    congr 1
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx hxv (by linarith)) (sq_nonneg _)

def levelMajorant (F : ℝ → ℂ) (a T v p : ℝ) (j : ℕ) : ℝ → ℝ :=
  (levelSet F a T ((2 : ℝ) ^ j * v)).indicator
    (fun _ => ((2 : ℝ) ^ (j + 1) * v) ^ p)

theorem majorant_nonnegative (F : ℝ → ℂ) (a T v p : ℝ) (hv : 0 ≤ v) (j : ℕ) (t : ℝ) :
    0 ≤ levelMajorant F a T v p j t := by
  unfold levelMajorant
  exact Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg (by positivity) _) t

theorem pointwise_bound (F : ℝ → ℂ) (a T v p : ℝ) (J : ℕ)
    (hv : 0 < v) (hp : 2 ≤ p) (t : ℝ) (ht : t ∈ Icc a (a + T))
    (hcap : ‖F t‖ ≤ (2 : ℝ) ^ J * v) :
    ‖F t‖ ^ p ≤ v ^ (p - 2) * ‖F t‖ ^ 2 +
      ∑ j ∈ Finset.range J, levelMajorant F a T v p j t := by
  have hsum : 0 ≤ ∑ j ∈ Finset.range J, levelMajorant F a T v p j t :=
    Finset.sum_nonneg (fun j _ => majorant_nonnegative F a T v p hv.le j t)
  by_cases hsmall : ‖F t‖ ≤ v
  · exact (small_value_bound ‖F t‖ v p (norm_nonneg _) hsmall hp).trans
      (le_add_of_nonneg_right hsum)
  · obtain ⟨j, hj, hlower, hupper⟩ := exists_band J v ‖F t‖ (lt_of_not_ge hsmall) hcap
    have hmember : t ∈ levelSet F a T ((2 : ℝ) ^ j * v) := ⟨ht, hlower.le⟩
    have hterm : levelMajorant F a T v p j t = ((2 : ℝ) ^ (j + 1) * v) ^ p :=
      Set.indicator_of_mem hmember _
    have hstep : ‖F t‖ ^ p ≤ levelMajorant F a T v p j t := by
      rw [hterm]
      exact Real.rpow_le_rpow (norm_nonneg _) hupper (by linarith)
    have hsingle := Finset.single_le_sum
      (fun k _ => majorant_nonnegative F a T v p hv.le k t) hj
    exact (hstep.trans hsingle).trans (le_add_of_nonneg_left (by positivity))

theorem integral_majorant (F : ℝ → ℂ) (a T v p : ℝ) (hF : Continuous F) (j : ℕ) :
    (∫ t in Icc a (a + T), levelMajorant F a T v p j t) =
      ((2 : ℝ) ^ (j + 1) * v) ^ p *
        volume.real (levelSet F a T ((2 : ℝ) ^ j * v)) := by
  unfold levelMajorant
  rw [setIntegral_indicator (measurable_levelSet F a T _ hF)]
  have hsub : levelSet F a T ((2 : ℝ) ^ j * v) ⊆ Icc a (a + T) := inter_subset_left
  rw [inter_eq_right.mpr hsub, integral_const]
  simp only [smul_eq_mul, measureReal_restrict_apply MeasurableSet.univ, univ_inter, mul_comm]

theorem integral_bound (F : ℝ → ℂ) (a T v p : ℝ) (J : ℕ)
    (hF : Continuous F) (hv : 0 < v) (hp : 2 ≤ p)
    (hcap : ∀ t ∈ Icc a (a + T), ‖F t‖ ≤ (2 : ℝ) ^ J * v) :
    (∫ t in Icc a (a + T), ‖F t‖ ^ p) ≤
      v ^ (p - 2) * (∫ t in Icc a (a + T), ‖F t‖ ^ 2) +
        ∑ j ∈ Finset.range J, ((2 : ℝ) ^ (j + 1) * v) ^ p *
          volume.real (levelSet F a T ((2 : ℝ) ^ j * v)) := by
  have hf : IntegrableOn (fun t => ‖F t‖ ^ p) (Icc a (a + T)) :=
    (hF.norm.rpow_const (fun _ => Or.inr (by linarith))).integrableOn_Icc
  have hbase : IntegrableOn (fun t => v ^ (p - 2) * ‖F t‖ ^ 2) (Icc a (a + T)) :=
    (continuous_const.mul (hF.norm.pow 2)).integrableOn_Icc
  have hterm (j : ℕ) : IntegrableOn (levelMajorant F a T v p j) (Icc a (a + T)) := by
    exact (integrable_const (((2 : ℝ) ^ (j + 1) * v) ^ p)).indicator
      (measurable_levelSet F a T _ hF)
  have hsum : IntegrableOn (fun t => ∑ j ∈ Finset.range J,
      levelMajorant F a T v p j t) (Icc a (a + T)) :=
    integrable_finsetSum _ (fun j _ => hterm j)
  calc
    _ ≤ ∫ t in Icc a (a + T), v ^ (p - 2) * ‖F t‖ ^ 2 +
        ∑ j ∈ Finset.range J, levelMajorant F a T v p j t :=
      setIntegral_mono_on hf (hbase.add hsum) measurableSet_Icc
        (fun t ht => pointwise_bound F a T v p J hv hp t ht (hcap t ht))
    _ = _ := by
      rw [integral_add hbase hsum, integral_const_mul,
        integral_finsetSum _ (fun j _ => hterm j)]
      simp_rw [integral_majorant F a T v p hF]

end DyadicMoment

#print axioms DyadicMoment.integral_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``DyadicMoment.integral_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "DYADIC MOMENT PASSED"
