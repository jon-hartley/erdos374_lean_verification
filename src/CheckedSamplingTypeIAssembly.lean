import CheckedSamplingTypeIWeights

/-!
The two complete Type I terms of Vaughan's identity, with their actual
Moebius, logarithmic, alpha and zeta coefficients.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace TypeIAssembly
open Erdos374.Vaughan145 Erdos374.ReciprocalCharacter151
open TypeIPrefix DyadicVaughan

theorem alpha_truncate (U M : ℕ) (f : ℕ → ℂ) :
    (∑ d ∈ Finset.Ioc 0 M, (alpha U U d : ℂ) * f d) =
      ∑ d ∈ Finset.Ioc 0 (min (U ^ 2) M), (alpha U U d : ℂ) * f d := by
  symm
  apply Finset.sum_subset
  · intro d hd
    simp only [Finset.mem_Ioc, le_min_iff] at hd ⊢
    omega
  · intro d hd hnot
    have hd' := Finset.mem_Ioc.mp hd
    have hbig : U * U < d := by
      simp only [Finset.mem_Ioc, le_min_iff] at hnot
      have hh : U ^ 2 < d := by omega
      nlinarith
    rw [alpha_zero_above_product hbig]
    simp

theorem zeta_inner_eq (P M d : ℕ) (u v : ℝ) :
    (∑ k ∈ Finset.Ioc (P / d) (M / d), (zetaR k : ℂ) * character u v (d * k)) =
      ∑ k ∈ Finset.Ioc (P / d) (M / d), character u v ((d : ℝ) * k) := by
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hk).1).ne'
  have hz : zetaR k = 1 := by
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hk0]
    norm_num
  simp only [hz, Complex.ofReal_one, one_mul]

theorem typeI_fourier (γ : ℝ) (hγ : 0 < γ) (A : ℕ) :
    ∃ B P₀ : ℕ, ∀ P M b : ℕ, P₀ ≤ P → P ≤ M → M ≤ 2 * P →
      1 ≤ b → (b : ℝ) ^ γ ≤ (P : ℝ) → ∀ n m : ℤ,
        n.natAbs + m.natAbs ≤ ⌈Real.log (P : ℝ) ^ 6⌉₊ →
        Real.log (P : ℝ) ^ B < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P →
        (‖∑ d ∈ Finset.Ioc 0 (min (cutoff P) M), (muR d : ℂ) *
          ∑ k ∈ Finset.Ioc (P / d) (M / d), (Real.log (k : ℝ) : ℂ) *
            character ((n : ℝ) * b) ((m : ℝ) * b) (d * k)‖ ≤
          (P : ℝ) / Real.log (P : ℝ) ^ A) ∧
        (‖∑ d ∈ Finset.Ioc 0 M, (alpha (cutoff P) (cutoff P) d : ℂ) *
          ∑ k ∈ Finset.Ioc (P / d) (M / d), (zetaR k : ℂ) *
            character ((n : ℝ) * b) ((m : ℝ) * b) (d * k)‖ ≤
          (P : ℝ) / Real.log (P : ℝ) ^ A) := by
  obtain ⟨B, N, hc⟩ := TypeIFourier.fourier_inner γ hγ (A + 4)
  obtain ⟨Nlog, hlog⟩ :=
    Erdos374.RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127 4
  refine ⟨B, max 512 (max N Nlog), ?_⟩
  intro P M b hP hPM hM hb hbgamma n m hfreq hlarge
  have hP512 : 512 ≤ P := by omega
  have hlogP := hlog P (by omega)
  have hlogPos : 0 < Real.log (P : ℝ) := by linarith
  have hcut := cutoff_properties P hP512
  have hcutSq := TypeIFourier.cutoff_square_le P hP512
  have hcut_le_sq : cutoff P ≤ cutoff P ^ 2 := by nlinarith [hcut.1]
  have hinner : ∀ d Q : ℕ, 0 < d → d ≤ cutoff P ^ 2 → Q ≤ 2 * P →
      ‖∑ k ∈ Finset.Ioc (P / d) (Q / d),
        character ((n : ℝ) * b) ((m : ℝ) * b) ((d : ℝ) * k)‖ ≤
        (prefixScale P d : ℝ) / Real.log (P : ℝ) ^ (A + 4) := by
    intro d Q hd hdU hQ
    exact hc P Q d b (by omega) hQ hd hdU hb hbgamma n m hfreq hlarge
  constructor
  · apply TypeIWeights.outer_sum_bound P (min (cutoff P) M) A _ (by omega)
      ((min_le_left _ _).trans hcut.2.1) hlogP
    intro d hd
    have hd' := Finset.mem_Ioc.mp hd
    have hdU : d ≤ cutoff P ^ 2 := (hd'.2.trans (min_le_left _ _)).trans hcut_le_sq
    have hdP : d ≤ P := hdU.trans hcutSq
    have hR : 0 ≤ (prefixScale P d : ℝ) / Real.log (P : ℝ) ^ (A + 4) := by positivity
    have hweighted := TypeIWeights.log_inner_bound P M d
      (fun k => character ((n : ℝ) * b) ((m : ℝ) * b) ((d : ℝ) * k))
      ((prefixScale P d : ℝ) / Real.log (P : ℝ) ^ (A + 4))
      hd'.1 hdP hPM hM hR (fun Q hQ => hinner d Q hd'.1 hdU hQ)
    have hlogquot := TypeIWeights.quotient_log_le P M d (by omega) hd'.1 hdP hPM hM
    have hweighted' : ‖∑ k ∈ Finset.Ioc (P / d) (M / d), (Real.log (k : ℝ) : ℂ) *
        character ((n : ℝ) * b) ((m : ℝ) * b) ((d : ℝ) * k)‖ ≤
        4 * Real.log (P : ℝ) * ((prefixScale P d : ℝ) / Real.log (P : ℝ) ^ (A + 4)) := by
      apply hweighted.trans
      exact mul_le_mul_of_nonneg_right (by linarith) hR
    have hmu : ‖(muR d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      change |(ArithmeticFunction.moebius d : ℝ)| ≤ 1
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    simp only [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hmu).trans hweighted'
  · rw [alpha_truncate]
    apply TypeIWeights.outer_sum_bound P (min (cutoff P ^ 2) M) A _ (by omega)
      ((min_le_left _ _).trans hcutSq) hlogP
    intro d hd
    have hd' := Finset.mem_Ioc.mp hd
    have hdU : d ≤ cutoff P ^ 2 := hd'.2.trans (min_le_left _ _)
    have hdP : d ≤ P := hdU.trans hcutSq
    have hR : 0 ≤ (prefixScale P d : ℝ) / Real.log (P : ℝ) ^ (A + 4) := by positivity
    have halpha : ‖(alpha (cutoff P) (cutoff P) d : ℂ)‖ ≤ Real.log (P : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (Erdos374.VaughanCoefficients152.alpha_abs_le_log _ _ _).trans
        (Real.log_le_log (Nat.cast_pos.mpr hd'.1) (Nat.cast_le.mpr hdP))
    rw [norm_mul, zeta_inner_eq]
    calc
      _ ≤ Real.log (P : ℝ) * ((prefixScale P d : ℝ) / Real.log (P : ℝ) ^ (A + 4)) :=
        mul_le_mul halpha (hinner d M hd'.1 hdU hM) (norm_nonneg _) hlogPos.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hR

end TypeIAssembly

#print axioms TypeIAssembly.typeI_fourier
run_cmd do
  let axioms ← Lean.collectAxioms ``TypeIAssembly.typeI_fourier
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "TYPE I ASSEMBLY PASSED"

run_cmd do
  for target in [``TypeIAssembly.alpha_truncate,
      ``TypeIAssembly.zeta_inner_eq,
      ``TypeIAssembly.typeI_fourier] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
