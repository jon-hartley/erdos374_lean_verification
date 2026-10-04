import CheckedSamplingTypeIPrefix

/-!
Apply Type I prefix cancellation to the exact integer Fourier frequencies,
including both coordinate axes, then restore the original inner intervals.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace TypeIFourier
open Erdos374.ReciprocalCharacter151 TypeIPrefix

theorem polynomial_prefix (J A : ℕ) :
    ∃ B P₀ : ℕ, ∀ P N T d b : ℕ, P₀ ≤ P → P ≤ N ^ 4 →
      P ≤ d * N → d * N ≤ 2 * P → 0 < d → T ≤ N →
      1 ≤ b → (b : ℝ) ≤ (P : ℝ) ^ J → ∀ n m : ℤ,
        n.natAbs + m.natAbs ≤ ⌈Real.log (P : ℝ) ^ 6⌉₊ →
        Real.log (P : ℝ) ^ B < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P →
        ‖∑ i ∈ Finset.range T, Erdos374.KusminLandau151.e
          (Erdos374.ReciprocalPhaseShape152.sequencePhase (N : ℝ)
            (((n : ℝ) * b) / d) (((m : ℝ) * b) / (d : ℝ) ^ 2) i)‖ ≤
          (N : ℝ) / Real.log (P : ℝ) ^ A := by
  obtain ⟨Br, Nr, hr⟩ := reciprocal_prefix J A
  obtain ⟨Bs, Ns, hs⟩ := square_prefix J A
  obtain ⟨Nf, hf⟩ := Erdos374.FourierReferenceIntegral152.frequency_threshold
  refine ⟨max Br Bs, max Nf (max Nr Ns), ?_⟩
  intro P N T d b hP hPN hprodLow hprodHigh hd hT hb hbUpper n m hfreq hlarge
  obtain ⟨_, hlog, hcut⟩ := hf P (by omega)
  have hbounds := FourierVaughanBands.frequency_bounds P n m hlog hcut hfreq
  have hbPos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hcoefficient : ∀ w : ℤ, |(w : ℝ)| ≤ (P : ℝ) →
      |(w : ℝ) * b| ≤ (P : ℝ) ^ (J + 1) := by
    intro w hw
    rw [abs_mul, abs_of_pos hbPos]
    calc
      _ ≤ (P : ℝ) * (P : ℝ) ^ J :=
        mul_le_mul hw hbUpper hbPos.le (Nat.cast_nonneg P)
      _ = _ := by rw [pow_succ]; ring
  by_cases hn : n = 0
  · subst n
    simp only [Int.cast_zero, zero_mul, zero_div] at hlarge ⊢
    have hlargeS := (pow_le_pow_right₀ hlog (le_max_right Br Bs)).trans_lt hlarge
    exact hs P N T d (by omega) hPN hprodHigh hd hT
      ((m : ℝ) * b) (hcoefficient m hbounds.2.1) hlargeS
  · have hu : (n : ℝ) * b ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hn) hbPos.ne'
    have hratio : |(m : ℝ) * b| ≤
        2 * Real.log (P : ℝ) ^ 6 * |(n : ℝ) * b| := by
      have hh := Erdos374.ReciprocalPhaseShape152.integer_coefficient_ratio_le
        n m b (2 * Real.log (P : ℝ) ^ 6) hn hbPos.ne' hbounds.2.2
      exact (div_le_iff₀ (abs_pos.mpr hu)).mp hh
    have hlargeR := (pow_le_pow_right₀ hlog (le_max_left Br Bs)).trans_lt hlarge
    exact hr P N T d (by omega) hPN hprodLow hprodHigh hd hT
      ((n : ℝ) * b) ((m : ℝ) * b) hu (hcoefficient n hbounds.1) hratio hlargeR

theorem fourier_prefix (γ : ℝ) (hγ : 0 < γ) (A : ℕ) :
    ∃ B P₀ : ℕ, ∀ P N T d b : ℕ, P₀ ≤ P → P ≤ N ^ 4 →
      P ≤ d * N → d * N ≤ 2 * P → 0 < d → T ≤ N →
      1 ≤ b → (b : ℝ) ^ γ ≤ (P : ℝ) → ∀ n m : ℤ,
        n.natAbs + m.natAbs ≤ ⌈Real.log (P : ℝ) ^ 6⌉₊ →
        Real.log (P : ℝ) ^ B < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P →
        ‖∑ i ∈ Finset.range T, Erdos374.KusminLandau151.e
          (Erdos374.ReciprocalPhaseShape152.sequencePhase (N : ℝ)
            (((n : ℝ) * b) / d) (((m : ℝ) * b) / (d : ℝ) ^ 2) i)‖ ≤
          (N : ℝ) / Real.log (P : ℝ) ^ A := by
  obtain ⟨J, hJ⟩ := FourierVaughanBands.polynomial_power_from_gamma γ hγ
  obtain ⟨B, P₀, hc⟩ := polynomial_prefix J A
  refine ⟨B, P₀, ?_⟩
  intro P N T d b hP hPN hprodLow hprodHigh hd hT hb hbgamma n m hfreq hlarge
  exact hc P N T d b hP hPN hprodLow hprodHigh hd hT hb
    (hJ P b hb hbgamma) n m hfreq hlarge

theorem inner_character_eq (P M d : ℕ) (u v : ℝ) :
    (∑ k ∈ Finset.Ioc (P / d) (M / d), character u v ((d : ℝ) * k)) =
      ∑ i ∈ Finset.range (M / d - P / d), Erdos374.KusminLandau151.e
        (Erdos374.ReciprocalPhaseShape152.sequencePhase (prefixScale P d : ℝ)
          (u / d) (v / (d : ℝ) ^ 2) i) := by
  simp_rw [Erdos374.BilinearCorrelation152.character_dilation]
  rw [Erdos374.BilinearCancellation152.character_Ioc_eq]
  simp only [prefixScale, Nat.cast_add, Nat.cast_one]

theorem cutoff_square_le (P : ℕ) (hP : 512 ≤ P) : DyadicVaughan.cutoff P ^ 2 ≤ P := by
  have hc := DyadicVaughan.cutoff_properties P hP
  have hh : DyadicVaughan.cutoff P ^ 2 ≤ DyadicVaughan.cutoff P ^ 3 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact hh.trans hc.2.2.1

theorem fourier_inner (γ : ℝ) (hγ : 0 < γ) (A : ℕ) :
    ∃ B P₀ : ℕ, ∀ P M d b : ℕ, P₀ ≤ P → M ≤ 2 * P →
      0 < d → d ≤ DyadicVaughan.cutoff P ^ 2 →
      1 ≤ b → (b : ℝ) ^ γ ≤ (P : ℝ) → ∀ n m : ℤ,
        n.natAbs + m.natAbs ≤ ⌈Real.log (P : ℝ) ^ 6⌉₊ →
        Real.log (P : ℝ) ^ B < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P →
        ‖∑ k ∈ Finset.Ioc (P / d) (M / d),
          character ((n : ℝ) * b) ((m : ℝ) * b) ((d : ℝ) * k)‖ ≤
          (prefixScale P d : ℝ) / Real.log (P : ℝ) ^ A := by
  obtain ⟨B, N, hc⟩ := fourier_prefix γ hγ A
  refine ⟨B, max 512 N, ?_⟩
  intro P M d b hP hM hd hdU hb hbgamma n m hfreq hlarge
  have hP512 : 512 ≤ P := by omega
  have hbounds := prefix_scale_bounds P d hd (hdU.trans (cutoff_square_le P hP512))
  rw [inner_character_eq]
  exact hc P (prefixScale P d) (M / d - P / d) d b (by omega)
    (prefix_fourth_power P d hP512 hd hdU) hbounds.1.le hbounds.2 hd
    (prefix_length_le P M d hd hM) hb hbgamma n m hfreq hlarge

end TypeIFourier

#print axioms TypeIFourier.fourier_inner
run_cmd do
  let axioms ← Lean.collectAxioms ``TypeIFourier.fourier_inner
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "TYPE I FOURIER PASSED"

run_cmd do
  for target in [``TypeIFourier.polynomial_prefix,
      ``TypeIFourier.fourier_prefix,
      ``TypeIFourier.inner_character_eq,
      ``TypeIFourier.cutoff_square_le,
      ``TypeIFourier.fourier_inner] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
