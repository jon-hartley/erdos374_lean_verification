import BoundaryMassBound

/-!
The existing nonnegative smoothing-boundary calculation extended to
complex weights. Only coefficient norms on the actual boundary band
enter the bound; a global coefficient bound would lose the 1/X scale.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ComplexSmoothingBoundary

def sharp (s : Finset ℕ) (a : ℕ → ℂ) (X : ℝ) : ℂ :=
  ∑ n ∈ s, if (n : ℝ) ≤ X then a n else 0

def smooth (s : Finset ℕ) (a : ℕ → ℂ) (ν : ℝ → ℝ) (epsilon X : ℝ) : ℂ :=
  ∑ n ∈ s, a n * (Smooth1 ν epsilon ((n : ℝ) / X) : ℂ)

theorem error_bound (s : Finset ℕ) (a : ℕ → ℂ) (ν : ℝ → ℝ)
    (epsilon X W : ℝ) (hX : 0 < X) (hepsilon : epsilon ∈ Ioo 0 1)
    (hW : 0 ≤ W) (hs : ∀ n ∈ s, 0 < n)
    (ha : ∀ n ∈ s, |(n : ℝ) / X - 1| ≤ (2 * Real.log 2) * epsilon → ‖a n‖ ≤ W)
    (hnonneg : ∀ x > 0, 0 ≤ ν x)
    (hsupport : Function.support ν ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, ν x / x = 1) :
    ‖smooth s a ν epsilon X - sharp s a X‖ ≤
      W * (4 * Real.log 2 * epsilon * X + 1) := by
  classical
  have hterm (n : ℕ) (hn : n ∈ s) :
      ‖a n * (Smooth1 ν epsilon ((n : ℝ) / X) : ℂ) -
          (if (n : ℝ) ≤ X then a n else 0)‖ ≤
        if |(n : ℝ) / X - 1| ≤ (2 * Real.log 2) * epsilon then W else 0 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hs n hn
    have hb := SmoothedCountBoundary.pointwise ν epsilon ((n : ℝ) / X)
      hepsilon (div_pos hnpos hX) hnonneg hsupport hmass
    have heq : (if (n : ℝ) ≤ X then a n else 0) =
        a n * (Complex.ofReal (if (n : ℝ) / X ≤ 1 then (1 : ℝ) else 0)) := by
      simp only [div_le_one hX]
      split_ifs <;> simp
    rw [heq, ← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hh := mul_le_mul_of_nonneg_left hb (norm_nonneg (a n))
    by_cases hband : |(n : ℝ) / X - 1| ≤ (2 * Real.log 2) * epsilon
    · simp only [ite_eq_left hband, mul_one] at hh ⊢
      exact hh.trans (ha n hn hband)
    · simpa only [ite_eq_right hband, mul_zero] using hh
  calc
    _ ≤ ∑ n ∈ s, if |(n : ℝ) / X - 1| ≤ (2 * Real.log 2) * epsilon then W else 0 := by
      rw [smooth, sharp, ← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ ≤ _ := BoundaryMassBound.boundary_bound s (fun _ => W) epsilon X W
      hX hepsilon.1.le hW (fun _ _ => le_rfl)

theorem cutoff_eq_finite (a : ℕ → ℂ) (ν : ℝ → ℝ) (epsilon X : ℝ) (N : ℕ)
    (ha : a 0 = 0) (hX : 0 < X) (hepsilon : epsilon ∈ Ioo 0 1)
    (hwidth : (2 * Real.log 2) * epsilon ≤ 1) (hN : 2 * X ≤ N)
    (hsupport : Function.support ν ⊆ Icc (1 / 2) 2) :
    (∑' n : ℕ, a n * (Smooth1 ν epsilon ((n : ℝ) / X) : ℂ)) =
      smooth (Finset.Ioc 0 N) a ν epsilon X := by
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0, ha]
  have hnN : N < n := by
    simp only [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hn
    omega
  have hnR : (N : ℝ) < n := by exact_mod_cast hnN
  obtain ⟨c, _, hc, habove⟩ := Smooth1Properties_above hsupport
  have hh := habove epsilon ((n : ℝ) / X) hepsilon (by
    rw [hc]
    apply (le_div_iff₀ hX).mpr
    nlinarith)
  simp only [hh, Complex.ofReal_zero, mul_zero]

end ComplexSmoothingBoundary

#print axioms ComplexSmoothingBoundary.error_bound
run_cmd do
  for target in [``ComplexSmoothingBoundary.error_bound,
      ``ComplexSmoothingBoundary.cutoff_eq_finite] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "COMPLEX SMOOTHING BOUNDARY PASSED"
