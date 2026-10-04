import CheckedSamplingUniformVaughanBands

/-!
Apply the uniform band bounds to the exact signed integer frequencies and
the b^gamma constraint in LargePhaseMangoldtCancellation.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace FourierVaughanBands
open Erdos374.Vaughan145 Erdos374.BilinearCorrelation152
open Erdos374.ReciprocalCharacter151

theorem polynomial_power_from_gamma (γ : ℝ) (hγ : 0 < γ) :
    ∃ J : ℕ, ∀ P b : ℕ, 1 ≤ b → (b : ℝ) ^ γ ≤ (P : ℝ) →
      (b : ℝ) ≤ (P : ℝ) ^ J := by
  obtain ⟨J, hJ⟩ := exists_nat_ge (1 / γ)
  refine ⟨J, ?_⟩
  intro P b hb hbound
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hγJ : 1 ≤ γ * (J : ℝ) := by
    have hh := (div_le_iff₀ hγ).mp hJ
    nlinarith only [hh]
  calc
    _ = (b : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (b : ℝ) ^ (γ * (J : ℝ)) := Real.rpow_le_rpow_of_exponent_le hbR hγJ
    _ = ((b : ℝ) ^ γ) ^ J := by
      rw [Real.rpow_mul (Nat.cast_nonneg b), Real.rpow_natCast]
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg b) γ) hbound J

theorem frequency_bounds (P : ℕ) (n m : ℤ)
    (hlog : 1 ≤ Real.log (P : ℝ))
    (hcut : 4 * (⌈Real.log (P : ℝ) ^ 6⌉₊ : ℝ) ≤ P)
    (hfreq : n.natAbs + m.natAbs ≤ ⌈Real.log (P : ℝ) ^ 6⌉₊) :
    |(n : ℝ)| ≤ (P : ℝ) ∧ |(m : ℝ)| ≤ (P : ℝ) ∧
      |(m : ℝ)| ≤ 2 * Real.log (P : ℝ) ^ 6 := by
  have hn : |(n : ℝ)| ≤ (⌈Real.log (P : ℝ) ^ 6⌉₊ : ℝ) := by
    have hh : n.natAbs ≤ ⌈Real.log (P : ℝ) ^ 6⌉₊ := by omega
    simpa only [Nat.cast_natAbs, Int.cast_abs] using (Nat.cast_le.mpr hh :
      (n.natAbs : ℝ) ≤ (⌈Real.log (P : ℝ) ^ 6⌉₊ : ℝ))
  have hm : |(m : ℝ)| ≤ (⌈Real.log (P : ℝ) ^ 6⌉₊ : ℝ) := by
    have hh : m.natAbs ≤ ⌈Real.log (P : ℝ) ^ 6⌉₊ := by omega
    simpa only [Nat.cast_natAbs, Int.cast_abs] using (Nat.cast_le.mpr hh :
      (m.natAbs : ℝ) ≤ (⌈Real.log (P : ℝ) ^ 6⌉₊ : ℝ))
  have hceilPos : (0 : ℝ) ≤ (⌈Real.log (P : ℝ) ^ 6⌉₊ : ℝ) := Nat.cast_nonneg _
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.log (P : ℝ) ^ 6 by positivity)
  have hpow : (1 : ℝ) ≤ Real.log (P : ℝ) ^ 6 := one_le_pow₀ hlog
  refine ⟨by linarith, by linarith, by linarith⟩

theorem polynomial_fourier_band (J A : ℕ) :
    ∃ B P₀ : ℕ, ∀ P D E K M U V b : ℕ, P₀ ≤ P →
      P ≤ D ^ 4 → P ≤ K ^ 4 → P ≤ 4 * (D * K) → D * K ≤ 2 * P → E ≤ 2 * D →
      1 ≤ b → (b : ℝ) ≤ (P : ℝ) ^ J → ∀ n m : ℤ,
        n.natAbs + m.natAbs ≤ ⌈Real.log (P : ℝ) ^ 6⌉₊ →
        Real.log (P : ℝ) ^ B < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P →
        ‖∑ d ∈ Finset.Ioc D E, (high U muR d : ℂ) *
          ∑ k ∈ Finset.Ioc K (2 * K), (beta V k : ℂ) *
            bandCharacter P M ((n : ℝ) * b) ((m : ℝ) * b) d k‖ ≤
          (P : ℝ) / Real.log (P : ℝ) ^ A := by
  obtain ⟨Br, Nr, hr⟩ := UniformVaughanBands.reciprocal_uniform_band J A
  obtain ⟨Bs, Ns, hs⟩ := UniformVaughanBands.square_uniform_band J A
  obtain ⟨Nf, hf⟩ := Erdos374.FourierReferenceIntegral152.frequency_threshold
  refine ⟨max Br Bs, max Nf (max Nr Ns), ?_⟩
  intro P D E K M U V b hP hPD hPK hDKlo hDKhi hE hb hbUpper n m hfreq hlarge
  obtain ⟨_, hlog, hcut⟩ := hf P (by omega)
  have hbounds := frequency_bounds P n m hlog hcut hfreq
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
    simp only [Int.cast_zero, zero_mul] at hlarge ⊢
    have hlargeS := (pow_le_pow_right₀ hlog (le_max_right Br Bs)).trans_lt hlarge
    exact hs P D E K M U V (by omega) hPD hPK hDKhi hE
      ((m : ℝ) * b) (hcoefficient m hbounds.2.1) hlargeS
  · have hu : (n : ℝ) * b ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hn) hbPos.ne'
    have hratio : |(m : ℝ) * b| ≤
        2 * Real.log (P : ℝ) ^ 6 * |(n : ℝ) * b| := by
      have hh := Erdos374.ReciprocalPhaseShape152.integer_coefficient_ratio_le
        n m b (2 * Real.log (P : ℝ) ^ 6) hn hbPos.ne' hbounds.2.2
      exact (div_le_iff₀ (abs_pos.mpr hu)).mp hh
    have hlargeR := (pow_le_pow_right₀ hlog (le_max_left Br Bs)).trans_lt hlarge
    exact hr P D E K M U V (by omega) hPD hPK hDKlo hDKhi hE
      ((n : ℝ) * b) ((m : ℝ) * b) hu (hcoefficient n hbounds.1) hratio hlargeR

/-- The exact b^gamma and signed integer-frequency range of the final
Mangoldt obligation, currently on one contributing Type II band. -/
theorem fourier_band (γ : ℝ) (hγ : 0 < γ) (A : ℕ) :
    ∃ B P₀ : ℕ, ∀ P D E K M U V b : ℕ, P₀ ≤ P →
      P ≤ D ^ 4 → P ≤ K ^ 4 → P ≤ 4 * (D * K) → D * K ≤ 2 * P → E ≤ 2 * D →
      1 ≤ b → (b : ℝ) ^ γ ≤ (P : ℝ) → ∀ n m : ℤ,
        n.natAbs + m.natAbs ≤ ⌈Real.log (P : ℝ) ^ 6⌉₊ →
        Real.log (P : ℝ) ^ B < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P →
        ‖∑ d ∈ Finset.Ioc D E, (high U muR d : ℂ) *
          ∑ k ∈ Finset.Ioc K (2 * K), (beta V k : ℂ) *
            bandCharacter P M ((n : ℝ) * b) ((m : ℝ) * b) d k‖ ≤
          (P : ℝ) / Real.log (P : ℝ) ^ A := by
  obtain ⟨J, hJ⟩ := polynomial_power_from_gamma γ hγ
  obtain ⟨B, P₀, hc⟩ := polynomial_fourier_band J A
  refine ⟨B, P₀, ?_⟩
  intro P D E K M U V b hP hPD hPK hDKlo hDKhi hE hb hbgamma n m hfreq hlarge
  exact hc P D E K M U V b hP hPD hPK hDKlo hDKhi hE hb
    (hJ P b hb hbgamma) n m hfreq hlarge

end FourierVaughanBands

#print axioms FourierVaughanBands.fourier_band
run_cmd do
  let axioms ← Lean.collectAxioms ``FourierVaughanBands.fourier_band
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOURIER VAUGHAN BANDS PASSED"

run_cmd do
  for target in [``FourierVaughanBands.polynomial_power_from_gamma,
      ``FourierVaughanBands.frequency_bounds,
      ``FourierVaughanBands.polynomial_fourier_band,
      ``FourierVaughanBands.fourier_band] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
