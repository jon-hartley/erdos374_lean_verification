import DirichletEvenMoment
import NormalizedEvenMoment
import GaussianMeanSquareWork
import PrimeReciprocalBoundsRefined

/-! Prime-supported polynomial powers have a constant collision bound.
The resulting even moments have no arbitrary positive power loss, and
are uniform in all complex coefficients (including Fourier phases). -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace PrimePowerMomentWork
open DirichletPowerCoefficients Erdos374.HarmanAnalytic151MeanSquare
open Erdos374.HarmanGram152

theorem fiber_card_le (s : Finset ℕ) (k n : ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    ((tuples s k).filter (fun f => productIndex f = n)).card ≤ k ^ k := by
  let F := (tuples s k).filter (fun f => productIndex f = n)
  by_cases hF : F.Nonempty
  · obtain ⟨f, hf⟩ := hF
    let P := Finset.univ.image f
    have hsub : F ⊆ Fintype.piFinset (fun _ : Fin k => P) := by
      intro g hg
      have hg' := Finset.mem_filter.mp hg
      apply Fintype.mem_piFinset.mpr
      intro i
      have hp := hs (g i) (Fintype.mem_piFinset.mp hg'.1 i)
      have hd : g i ∣ ∏ j, f j := by
        change g i ∣ productIndex f
        rw [(Finset.mem_filter.mp hf).2, ← hg'.2]
        exact Finset.dvd_prod_of_mem g (Finset.mem_univ i)
      obtain ⟨j, _, hj⟩ := (hp.prime.dvd_finsetProd_iff f).mp hd
      have hq := hs (f j) (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 j)
      have he : g i = f j := (Nat.dvd_prime hq).mp hj |>.resolve_left hp.ne_one
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, he.symm⟩
    have hP : P.card ≤ k := by
      exact Finset.card_image_le.trans_eq (by simp)
    calc
      F.card ≤ (Fintype.piFinset (fun _ : Fin k => P)).card := Finset.card_le_card hsub
      _ = P.card ^ k := by simp
      _ ≤ k ^ k := Nat.pow_le_pow_left hP k
  · change F.card ≤ k ^ k
    rw [Finset.not_nonempty_iff_eq_empty.mp hF, Finset.card_empty]
    exact Nat.zero_le _

theorem energy_bound (s : Finset ℕ) (k L : ℕ) (coeff : ℕ → ℂ)
    (hs : ∀ p ∈ s, Nat.Prime p ∧ p ≤ L) :
    (∑ n ∈ Finset.Icc 1 (L ^ k), ‖coefficient s k coeff n‖ ^ 2) ≤
      (k ^ k : ℕ) * (∑ p ∈ s, ‖coeff p‖ ^ 2) ^ k := by
  apply DirichletPowerCoefficients.energy_bound s (Finset.Icc 1 (L ^ k)) k coeff
    (k ^ k : ℕ)
  · intro f hf
    exact Finset.mem_Icc.mpr
      ⟨product_positive s k (fun p hp => (hs p hp).1.pos) f hf,
        product_le s k L (fun p hp => (hs p hp).2) f hf⟩
  · intro n _
    exact_mod_cast fiber_card_le s k n (fun p hp => (hs p hp).1)

theorem integral_bound (s : Finset ℕ) (k L : ℕ) (coeff : ℕ → ℂ) (a T : ℝ)
    (hL : 1 ≤ L) (hT : 0 ≤ T) (hs : ∀ p ∈ s, Nat.Prime p ∧ p ≤ L) :
    (∫ t in Icc a (a + T),
      ‖exponentialSum151 s coeff (fun p => Real.log p) t‖ ^ (2 * k)) ≤
      (k ^ k : ℕ) *
        (T + 4 * (L ^ k : ℕ) * (1 + Real.log (L ^ k : ℕ))) *
          (∑ p ∈ s, ‖coeff p‖ ^ 2) ^ k := by
  have hlen : (1 : ℝ) ≤ (L ^ k : ℕ) := by exact_mod_cast one_le_pow₀ hL
  have hlog : 0 ≤ Real.log (L ^ k : ℕ) := Real.log_nonneg hlen
  have hm := dirichlet_mean_square_le151 (Finset.Icc 1 (L ^ k))
    (coefficient s k coeff) (L ^ k) (fun n hn => Finset.mem_Icc.mp hn) a (a + T)
  simp only [add_sub_cancel_left] at hm
  have hh := hm.trans (mul_le_mul_of_nonneg_left (energy_bound s k L coeff hs)
    (show 0 ≤ T + 4 * (L ^ k : ℕ) * (1 + Real.log (L ^ k : ℕ)) by positivity))
  simp_rw [DirichletPowerExpansion.norm_power s k L coeff _
    (fun p hp => ⟨(hs p hp).1.pos, (hs p hp).2⟩)]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show a ≤ a + T by linarith)]
  exact hh.trans_eq (by ring)

theorem normalized_integral_bound (s : Finset ℕ) (k N : ℕ)
    (coeff : ℕ → ℂ) (a T A σ : ℝ) (hN : 1 ≤ N) (hT : 0 ≤ T) (hσ : 1 ≤ σ)
    (hs : ∀ p ∈ s, Nat.Prime p ∧ N ≤ p ∧ p ≤ 2 * N)
    (henergy : (∑ p ∈ s, ‖coeff p‖ ^ 2) ≤ A * N) :
    (∫ t in Icc a (a + T), ‖verticalDirichlet152 s coeff σ t‖ ^ (2 * k)) ≤
      (k ^ k : ℕ) * A ^ k *
        (T / (N : ℝ) ^ k + 4 * (2 : ℝ) ^ k * (1 + k * Real.log (2 * N))) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs0 : ∀ p ∈ s, 0 < p := fun p hp => (hs p hp).1.pos
  let weighted : ℕ → ℂ := fun p => conj (normalizedCoefficients152 coeff σ p)
  have he : (∑ p ∈ s, ‖weighted p‖ ^ 2) ≤ A / N := by
    dsimp [weighted]
    simp only [RCLike.norm_conj]
    apply (normalized_coefficients_energy152 s coeff N hN σ hσ
      (fun p hp => (hs p hp).2.1)).trans
    calc
      _ ≤ (A * N) / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right henergy (sq_nonneg _)
      _ = _ := by field_simp
  have hsum : 0 ≤ ∑ p ∈ s, ‖weighted p‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hlog : 0 ≤ Real.log (((2 * N) ^ k : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast one_le_pow₀ (show 1 ≤ 2 * N by omega) (n := k))
  have hf : 0 ≤ (k ^ k : ℕ) *
      (T + 4 * ((2 * N) ^ k : ℕ) * (1 + Real.log ((2 * N) ^ k : ℕ))) := by positivity
  have hh := (integral_bound s k (2 * N) weighted a T (by omega) hT
    (fun p hp => ⟨(hs p hp).1, (hs p hp).2.2⟩)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum he k) hf)
  simp_rw [verticalDirichlet_norm152 s coeff σ _ hs0]
  apply hh.trans_eq
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.log_pow, div_pow, mul_pow]
  field_simp

theorem sharp_integral_bound (s : Finset ℕ) (k L : ℕ) (coeff : ℕ → ℂ) (a T : ℝ)
    (hL : 1 ≤ L) (hT : 0 ≤ T) (hTL : T ≤ (L ^ k : ℕ))
    (hs : ∀ p ∈ s, Nat.Prime p ∧ p ≤ L) :
    (∫ t in Icc a (a+T),
      ‖exponentialSum151 s coeff (fun p => Real.log p) t‖ ^ (2*k)) ≤
      GaussianMeanSquareWork.meanSquareConstant * (L ^ k : ℕ) * (k ^ k : ℕ) *
        (∑ p ∈ s, ‖coeff p‖^2)^k := by
  have hLk : 1 ≤ L^k := one_le_pow₀ hL
  have hm := GaussianMeanSquareWork.dirichlet_mean_square_max (Finset.Icc 1 (L^k))
    (coefficient s k coeff) (L^k) a T hLk hT (fun n hn => Finset.mem_Icc.mp hn)
  rw [max_eq_right hTL] at hm
  have hh := hm.trans (mul_le_mul_of_nonneg_left (energy_bound s k L coeff hs)
    (mul_nonneg GaussianMeanSquareWork.meanSquareConstant_pos.le (Nat.cast_nonneg _)))
  simp_rw [DirichletPowerExpansion.norm_power s k L coeff _
    (fun p hp => ⟨(hs p hp).1.pos, (hs p hp).2⟩)]
  exact hh.trans_eq (by ring)

theorem sharp_normalized_integral_bound (s : Finset ℕ) (k N : ℕ)
    (coeff : ℕ → ℂ) (a T A σ : ℝ) (hN : 1 ≤ N) (hT : 0 ≤ T) (hσ : 1 ≤ σ)
    (hTN : T ≤ ((2*N)^k : ℕ))
    (hs : ∀ p ∈ s, Nat.Prime p ∧ N ≤ p ∧ p ≤ 2*N)
    (henergy : (∑ p ∈ s, ‖coeff p‖^2) ≤ A*N) :
    (∫ t in Icc a (a+T), ‖verticalDirichlet152 s coeff σ t‖^(2*k)) ≤
      GaussianMeanSquareWork.meanSquareConstant * (k^k : ℕ) * (2 : ℝ)^k * A^k := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs0 : ∀ p ∈ s, 0 < p := fun p hp => (hs p hp).1.pos
  let weighted : ℕ → ℂ := fun p => conj (normalizedCoefficients152 coeff σ p)
  have he : (∑ p ∈ s, ‖weighted p‖^2) ≤ A/N := by
    dsimp [weighted]
    simp only [RCLike.norm_conj]
    apply (normalized_coefficients_energy152 s coeff N hN σ hσ
      (fun p hp => (hs p hp).2.1)).trans
    calc
      _ ≤ (A*N)/(N : ℝ)^2 := div_le_div_of_nonneg_right henergy (sq_nonneg _)
      _ = _ := by field_simp
  have hh := (sharp_integral_bound s k (2*N) weighted a T (by omega) hT hTN
    (fun p hp => ⟨(hs p hp).1, (hs p hp).2.2⟩)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) he k)
        (show 0 ≤ GaussianMeanSquareWork.meanSquareConstant * ((2*N)^k : ℕ) * (k^k : ℕ) by
          exact mul_nonneg (mul_nonneg GaussianMeanSquareWork.meanSquareConstant_pos.le
            (Nat.cast_nonneg _)) (Nat.cast_nonneg _)))
  simp_rw [verticalDirichlet_norm152 s coeff σ _ hs0]
  apply hh.trans_eq
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, div_pow, mul_pow]
  field_simp

theorem eventual_unit_prime_moment (k : ℕ) :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ N : ℕ, W ≤ (N : ℝ) →
      ∀ (s : Finset ℕ) (coeff : ℕ → ℂ) (a T σ : ℝ), 0 ≤ T → 1 ≤ σ →
        T ≤ ((2*N)^k : ℕ) →
        (∀ p ∈ s, Nat.Prime p ∧ N ≤ p ∧ p ≤ 2*N) →
        (∀ p ∈ s, ‖coeff p‖ ≤ 1) →
        (∫ t in Icc a (a+T), ‖verticalDirichlet152 s coeff σ t‖^(2*k)) ≤
          (GaussianMeanSquareWork.meanSquareConstant * (k^k : ℕ) * (8 : ℝ)^k) /
            (Real.log N)^k := by
  obtain ⟨W, hW, hcount⟩ := PrimeReciprocalBoundsRefined.eventual_primeCounting_bound_two
  refine ⟨W, hW, ?_⟩
  intro N hNW s coeff a T σ hT hσ hTN hs hw
  have hN2 : (2 : ℝ) ≤ N := hW.trans hNW
  have hN : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have hNp : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hsub : s ⊆ Nat.primesLE (2*N) := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(hs p hp).2.2, (hs p hp).1⟩
  have hcard : (s.card : ℝ) ≤ 4*N/Real.log N := by
    calc
      _ ≤ ((Nat.primesLE (2*N)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = (Nat.primeCounting (2*N) : ℝ) := by rw [Nat.primesLE_card_eq_primeCounting]
      _ ≤ 2*(2*N)/Real.log (2*N) := by
        have hh := hcount ((2*N : ℕ) : ℝ) (by
          simp only [Nat.cast_mul, Nat.cast_ofNat]
          linarith)
        rw [Nat.floor_natCast] at hh
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
      _ ≤ 4*N/Real.log N := by
        have hl : Real.log N ≤ Real.log (2*N) := Real.log_le_log hNp (by linarith)
        convert div_le_div_of_nonneg_left (show 0 ≤ 4*(N : ℝ) by positivity) hlog hl using 1
        ring
  have he : (∑ p ∈ s, ‖coeff p‖^2) ≤ (4/Real.log N)*N := by
    calc
      _ ≤ ∑ _p ∈ s, (1 : ℝ) := Finset.sum_le_sum (fun p hp => by
        have hh := pow_le_pow_left₀ (norm_nonneg _) (hw p hp) 2
        simpa using hh)
      _ = (s.card : ℝ) := by simp
      _ ≤ 4*N/Real.log N := hcard
      _ = _ := by ring
  apply (sharp_normalized_integral_bound s k N coeff a T (4/Real.log N) σ
    hN hT hσ hTN hs he).trans_eq
  rw [div_pow]
  field_simp
  rw [show (8 : ℝ) = 2*4 by norm_num, mul_pow]
  ring

#print axioms eventual_unit_prime_moment
#print axioms normalized_integral_bound
run_cmd do
  for decl in [``fiber_card_le, ``energy_bound, ``integral_bound,
      ``normalized_integral_bound, ``sharp_integral_bound,
      ``sharp_normalized_integral_bound, ``eventual_unit_prime_moment] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "PRIME POWER MOMENTS PASSED; no positive power loss"
end PrimePowerMomentWork
