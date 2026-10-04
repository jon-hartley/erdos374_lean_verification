import CheckedSamplingTypeIFourier

/-!
Logarithmic weight insertion and the harmonic cost of the outer Type I sum.
These estimates retain the actual prefix scales and integer endpoints.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace TypeIWeights
open Erdos374.ReciprocalCharacter151 TypeIPrefix

theorem log_inner_bound (P M d : ℕ) (c : ℕ → ℂ) (R : ℝ)
    (hd : 0 < d) (hdP : d ≤ P) (hPM : P ≤ M) (hM : M ≤ 2 * P)
    (hR : 0 ≤ R)
    (hprefix : ∀ Q : ℕ, Q ≤ 2 * P → ‖∑ k ∈ Finset.Ioc (P / d) (Q / d), c k‖ ≤ R) :
    ‖∑ k ∈ Finset.Ioc (P / d) (M / d), (Real.log (k : ℝ) : ℂ) * c k‖ ≤
      2 * Real.log ((M / d : ℕ) : ℝ) * R := by
  apply Erdos374.LogWeightInsertion152.log_weight_insertion_coarse (P / d) (M / d)
    (by exact (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdP))
    (Nat.div_le_div_right hPM) c R hR
  intro K hKlo hKhi
  have hprod : d * K ≤ 2 * P := by
    have hh := (Nat.le_div_iff_mul_le hd).mp hKhi
    nlinarith
  simpa only [Nat.mul_div_cancel_left K hd] using hprefix (d * K) hprod

theorem quotient_log_le (P M d : ℕ) (hP : 2 ≤ P) (hd : 0 < d)
    (hdP : d ≤ P) (hPM : P ≤ M) (hM : M ≤ 2 * P) :
    Real.log ((M / d : ℕ) : ℝ) ≤ 2 * Real.log (P : ℝ) := by
  have hquot : 1 ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdP.trans hPM)
  have hqpos : (0 : ℝ) < (M / d : ℕ) := by exact_mod_cast (show 0 < M / d by omega)
  have hqhi : ((M / d : ℕ) : ℝ) ≤ (P : ℝ) ^ 2 := by
    have hh : M / d ≤ 2 * P := (Nat.div_le_self M d).trans hM
    have hhR : ((M / d : ℕ) : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hh
    have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
    nlinarith
  have hh := Real.log_le_log hqpos hqhi
  simpa only [Real.log_pow, Nat.cast_ofNat] using hh

theorem prefix_scale_sum (P D : ℕ) (hP : 1 ≤ P) (hD : D ≤ P)
    (hlog : 1 ≤ Real.log (P : ℝ)) :
    (∑ d ∈ Finset.Ioc 0 D, (prefixScale P d : ℝ)) ≤ 4 * (P : ℝ) * Real.log (P : ℝ) := by
  have hfull : (∑ d ∈ Finset.Ioc 0 P, (prefixScale P d : ℝ)) ≤
      2 * (P : ℝ) * (1 + Real.log (P : ℝ)) := by
    calc
      _ ≤ ∑ d ∈ Finset.Ioc 0 P, 2 * (P : ℝ) * (d : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro d hd
        have hd' := Finset.mem_Ioc.mp hd
        have hdr : (0 : ℝ) < d := Nat.cast_pos.mpr hd'.1
        have hb := (prefix_scale_bounds P d hd'.1 hd'.2).2
        have hbR : (d : ℝ) * (prefixScale P d : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hb
        rw [← div_eq_mul_inv]
        apply (le_div_iff₀ hdr).mpr
        nlinarith only [hbR]
      _ = 2 * (P : ℝ) * (harmonic P : ℝ) := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
        push_cast
        congr 2
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log P) (by positivity)
  have hsubset : Finset.Ioc 0 D ⊆ Finset.Ioc 0 P := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd ⊢
    omega
  have hsmall := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun d hd hnot => Nat.cast_nonneg (prefixScale P d) : ∀ d ∈ Finset.Ioc 0 P,
      d ∉ Finset.Ioc 0 D → (0 : ℝ) ≤ prefixScale P d)
  have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * (P : ℝ) by positivity)
  linarith only [hsmall, hfull, hh]

theorem outer_sum_bound (P D A : ℕ) (f : ℕ → ℂ)
    (hP : 1 ≤ P) (hD : D ≤ P) (hlog : 4 ≤ Real.log (P : ℝ))
    (hterm : ∀ d ∈ Finset.Ioc 0 D, ‖f d‖ ≤
      4 * Real.log (P : ℝ) * ((prefixScale P d : ℝ) / Real.log (P : ℝ) ^ (A + 4))) :
    ‖∑ d ∈ Finset.Ioc 0 D, f d‖ ≤ (P : ℝ) / Real.log (P : ℝ) ^ A := by
  have hlogPos : 0 < Real.log (P : ℝ) := by linarith
  have hsum := prefix_scale_sum P D hP hD (by linarith)
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 0 D, ‖f d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 D,
        4 * Real.log (P : ℝ) * ((prefixScale P d : ℝ) / Real.log (P : ℝ) ^ (A + 4)) :=
      Finset.sum_le_sum hterm
    _ = (4 * Real.log (P : ℝ) / Real.log (P : ℝ) ^ (A + 4)) *
        ∑ d ∈ Finset.Ioc 0 D, (prefixScale P d : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (4 * Real.log (P : ℝ) / Real.log (P : ℝ) ^ (A + 4)) *
        (4 * (P : ℝ) * Real.log (P : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (16 / Real.log (P : ℝ) ^ 2) * ((P : ℝ) / Real.log (P : ℝ) ^ A) := by
      rw [pow_add (Real.log (P : ℝ)) A 4]
      field_simp
      ring
    _ ≤ 1 * ((P : ℝ) / Real.log (P : ℝ) ^ A) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply (div_le_one (by positivity : 0 < Real.log (P : ℝ) ^ 2)).mpr
      nlinarith
    _ = _ := one_mul _

end TypeIWeights

#print axioms TypeIWeights.outer_sum_bound
run_cmd do
  for target in [``TypeIWeights.log_inner_bound, ``TypeIWeights.quotient_log_le,
      ``TypeIWeights.prefix_scale_sum, ``TypeIWeights.outer_sum_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "TYPE I WEIGHTS PASSED"

run_cmd do
  for target in [``TypeIWeights.log_inner_bound,
      ``TypeIWeights.quotient_log_le,
      ``TypeIWeights.prefix_scale_sum,
      ``TypeIWeights.outer_sum_bound] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
