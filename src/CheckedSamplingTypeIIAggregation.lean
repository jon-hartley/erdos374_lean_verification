import CheckedSamplingVaughanPartition

/-!
Sum every dyadic Vaughan band, including the zero blocks, to obtain a
uniform bound for the full Type II convolution at the chosen cutoffs.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace TypeIIAggregation
open Erdos374.Vaughan145 Erdos374.BilinearCorrelation152
open Erdos374.ReciprocalCharacter151 DyadicVaughan

theorem band_zero_of_outer (U V P M D K : ℕ) (u v : ℝ)
    (hD : 2 * D ≤ U) :
    (∑ d ∈ Finset.Ioc D (2 * D), (high U muR d : ℂ) *
      ∑ k ∈ Finset.Ioc K (2 * K), (beta V k : ℂ) *
        bandCharacter P M u v d k) = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  rw [high_zero_of_le muR ((Finset.mem_Ioc.mp hd).2.trans hD)]
  simp

theorem band_zero_of_inner (U V P M D K : ℕ) (u v : ℝ)
    (hK : 2 * K ≤ V) :
    (∑ d ∈ Finset.Ioc D (2 * D), (high U muR d : ℂ) *
      ∑ k ∈ Finset.Ioc K (2 * K), (beta V k : ℂ) *
        bandCharacter P M u v d k) = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  suffices (∑ k ∈ Finset.Ioc K (2 * K), (beta V k : ℂ) *
      bandCharacter P M u v d k) = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro k hk
  rw [beta_zero_of_le ((Finset.mem_Ioc.mp hk).2.trans hK)]
  simp

theorem band_zero_of_product (U V P M D K : ℕ) (u v : ℝ)
    (hM : M ≤ 2 * P) (hprod : 4 * (D * K) < P ∨ 2 * P < D * K) :
    (∑ d ∈ Finset.Ioc D (2 * D), (high U muR d : ℂ) *
      ∑ k ∈ Finset.Ioc K (2 * K), (beta V k : ℂ) *
        bandCharacter P M u v d k) = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  suffices (∑ k ∈ Finset.Ioc K (2 * K), (beta V k : ℂ) *
      bandCharacter P M u v d k) = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro k hk
  have hd' := Finset.mem_Ioc.mp hd
  have hk' := Finset.mem_Ioc.mp hk
  have hout : ¬(P < d * k ∧ d * k ≤ M) := by
    intro hbad
    rcases hprod with hlo | hhi
    · have hh := Nat.mul_le_mul hd'.2 hk'.2
      nlinarith
    · have hh := Nat.mul_le_mul hd'.1.le hk'.1.le
      omega
  simp [bandCharacter, hout]

theorem all_dyadic_bands (γ : ℝ) (hγ : 0 < γ) (A : ℕ) :
    ∃ B P₀ : ℕ, ∀ P M b j h : ℕ, P₀ ≤ P → M ≤ 2 * P →
      1 ≤ b → (b : ℝ) ^ γ ≤ (P : ℝ) → ∀ n m : ℤ,
        n.natAbs + m.natAbs ≤ ⌈Real.log (P : ℝ) ^ 6⌉₊ →
        Real.log (P : ℝ) ^ B < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P →
        ‖∑ d ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)),
          (high (cutoff P) muR d : ℂ) *
            ∑ k ∈ Finset.Ioc (2 ^ h) (2 ^ (h + 1)),
              (beta (cutoff P) k : ℂ) *
                bandCharacter P M ((n : ℝ) * b) ((m : ℝ) * b) d k‖ ≤
          (P : ℝ) / Real.log (P : ℝ) ^ A := by
  obtain ⟨B, N, hc⟩ := FourierVaughanBands.fourier_band γ hγ A
  refine ⟨B, max 512 N, ?_⟩
  intro P M b j h hP hM hb hbgamma n m hfreq hlarge
  have hcut := cutoff_properties P (by omega)
  have htarget : 0 ≤ (P : ℝ) / Real.log (P : ℝ) ^ A := by
    have : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ P by omega))
    positivity
  simp only [pow_succ, Nat.mul_comm _ 2]
  by_cases hj : j < cutoffExponent P
  · have hlow : 2 * 2 ^ j ≤ cutoff P := by
      simpa only [cutoff, pow_succ, Nat.mul_comm _ 2] using
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (show j + 1 ≤ cutoffExponent P by omega)
    rw [band_zero_of_outer _ _ _ _ _ _ _ _ hlow, norm_zero]
    exact htarget
  by_cases hh : h < cutoffExponent P
  · have hlow : 2 * 2 ^ h ≤ cutoff P := by
      simpa only [cutoff, pow_succ, Nat.mul_comm _ 2] using
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (show h + 1 ≤ cutoffExponent P by omega)
    rw [band_zero_of_inner _ _ _ _ _ _ _ _ hlow, norm_zero]
    exact htarget
  by_cases hlo : P ≤ 4 * (2 ^ j * 2 ^ h)
  · by_cases hhi : 2 ^ j * 2 ^ h ≤ 2 * P
    · have hD : cutoff P ≤ 2 ^ j :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
      have hK : cutoff P ≤ 2 ^ h :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
      exact hc P (2 ^ j) (2 * 2 ^ j) (2 ^ h) M (cutoff P) (cutoff P) b
        (by omega) (hcut.2.2.2.trans (Nat.pow_le_pow_left hD 4))
        (hcut.2.2.2.trans (Nat.pow_le_pow_left hK 4)) hlo hhi (by omega)
        hb hbgamma n m hfreq hlarge
    · rw [band_zero_of_product _ _ _ _ _ _ _ _ hM (Or.inr (by omega)), norm_zero]
      exact htarget
  · rw [band_zero_of_product _ _ _ _ _ _ _ _ hM (Or.inl (by omega)), norm_zero]
    exact htarget

theorem double_norm_sum_le (L : ℕ) (f : ℕ → ℕ → ℂ) (T : ℝ)
    (hbound : ∀ j ∈ Finset.range L, ∀ h ∈ Finset.range L, ‖f j h‖ ≤ T) :
    ‖∑ j ∈ Finset.range L, ∑ h ∈ Finset.range L, f j h‖ ≤ (L : ℝ) ^ 2 * T := by
  calc
    _ ≤ ∑ j ∈ Finset.range L, ‖∑ h ∈ Finset.range L, f j h‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range L, ∑ h ∈ Finset.range L, ‖f j h‖ :=
      Finset.sum_le_sum (fun j hj => norm_sum_le _ _)
    _ ≤ ∑ j ∈ Finset.range L, ∑ h ∈ Finset.range L, T := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_le_sum (fun h hh => hbound j hj h hh)
    _ = _ := by simp; ring

theorem logarithmic_aggregation (P L : ℝ) (A : ℕ)
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hlog : 25 ≤ Real.log P)
    (hcount : L ≤ 5 * Real.log P) :
    L ^ 2 * (P / Real.log P ^ (A + 3)) ≤ P / Real.log P ^ A := by
  have hlogPos : 0 < Real.log P := by linarith
  have hsquare : L ^ 2 ≤ 25 * Real.log P ^ 2 := by
    have hh := pow_le_pow_left₀ hL hcount 2
    nlinarith only [hh]
  have hcube : L ^ 2 ≤ Real.log P ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right hlog (sq_nonneg (Real.log P))
    nlinarith only [hh, hsquare]
  calc
    _ = (L ^ 2 * P) / Real.log P ^ (A + 3) := by ring
    _ ≤ (Real.log P ^ 3 * P) / Real.log P ^ (A + 3) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcube hP) (by positivity)
    _ = _ := by rw [pow_add]; field_simp

theorem typeII_fourier (γ : ℝ) (hγ : 0 < γ) (A : ℕ) :
    ∃ B P₀ : ℕ, ∀ P M b : ℕ, P₀ ≤ P → M ≤ 2 * P →
      1 ≤ b → (b : ℝ) ^ γ ≤ (P : ℝ) → ∀ n m : ℤ,
        n.natAbs + m.natAbs ≤ ⌈Real.log (P : ℝ) ^ 6⌉₊ →
        Real.log (P : ℝ) ^ B < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P →
        ‖phaseSum (Finset.Ioc P M)
          (fun t => character ((n : ℝ) * b) ((m : ℝ) * b) t)
          (high (cutoff P) muR * beta (cutoff P))‖ ≤
          (P : ℝ) / Real.log (P : ℝ) ^ A := by
  obtain ⟨B, N, hc⟩ := all_dyadic_bands γ hγ (A + 3)
  obtain ⟨Nlog, hlog⟩ :=
    Erdos374.RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127 25
  refine ⟨B, max 512 (max N Nlog), ?_⟩
  intro P M b hP hM hb hbgamma n m hfreq hlarge
  have hcut := cutoff_properties P (by omega)
  have hlogP := hlog P (by omega)
  rw [VaughanPartition.typeII_dyadic_identity _ _ _ _ (bandCount P) _ _
    (by omega) (by omega) (hM.trans (band_count_covers P))]
  apply (double_norm_sum_le (bandCount P) _ ((P : ℝ) / Real.log (P : ℝ) ^ (A + 3)) ?_).trans
  · exact logarithmic_aggregation P (bandCount P) A (Nat.cast_nonneg P)
      (Nat.cast_nonneg _) hlogP (band_count_le_log P (by omega) (by linarith))
  · intro j hj h hh
    exact hc P M b j h (by omega) hM hb hbgamma n m hfreq hlarge

end TypeIIAggregation

#print axioms TypeIIAggregation.typeII_fourier
run_cmd do
  let axioms ← Lean.collectAxioms ``TypeIIAggregation.typeII_fourier
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "TYPE II AGGREGATION PASSED"

run_cmd do
  for target in [``TypeIIAggregation.band_zero_of_outer,
      ``TypeIIAggregation.band_zero_of_inner,
      ``TypeIIAggregation.band_zero_of_product,
      ``TypeIIAggregation.all_dyadic_bands,
      ``TypeIIAggregation.double_norm_sum_le,
      ``TypeIIAggregation.logarithmic_aggregation,
      ``TypeIIAggregation.typeII_fourier] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
