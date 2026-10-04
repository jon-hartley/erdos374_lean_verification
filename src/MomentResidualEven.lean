import MomentResidualInterval

/-! Fresh proof adaptation of the retained 162 reference source. All imports belong
to the current verified closure or to this new branch; no old object is used.
Actual von Mangoldt coefficients include all prime powers. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators ComplexConjugate
open Set Filter MeasureTheory
namespace MomentResidualEven
open MomentResidualConvolution MomentResidualInterval
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare
theorem finiteDirichlet_power_of_support (a : ArithmeticFunction ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : ∀ n, N < n → a n = 0) (h : ℕ) (z : ℂ) :
    finiteDirichlet N a z ^ h = finiteDirichlet (N^h) (a^h) z := by
  induction h with
  | zero => simp [finiteDirichlet, show Finset.Ioc 0 1 = {1} by decide,
      ArithmeticFunction.one_apply]
  | succ h ih =>
    rw [pow_succ a, pow_succ N,
      finiteDirichlet_mul (N^h) N (one_le_pow₀ hN) hN (a^h) a
        (fun n hn => power_vanishes_above a N ha h n hn) ha z,
      ← ih, pow_succ]

theorem interval_dirichlet (D N : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    finiteDirichlet N (intervalCoefficients D N a) z =
      ∑ n ∈ Finset.Ioc D N, a n * (n : ℂ)^z := by
  unfold finiteDirichlet
  calc
    _ = ∑ n ∈ Finset.Ioc D N, intervalCoefficients D N a n * (n : ℂ)^z := by
      symm
      apply Finset.sum_subset (Finset.Ioc_subset_Ioc (Nat.zero_le _) le_rfl)
      intro n hn hnot
      simp [hnot]
    _ = _ := Finset.sum_congr rfl (by intro n hn; simp [hn])

theorem interval_vertical_power (D N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ)
    (h : ℕ) (σ t : ℝ) :
    verticalDirichlet152 (Finset.Ioc D N) a σ t ^ h =
      verticalDirichlet152 (Finset.Ioc 0 (N^h))
        (fun n => (intervalCoefficients D N a ^ h) n) σ t := by
  have hp := finiteDirichlet_power_of_support (intervalCoefficients D N a) N hN
    (by intro n hn; simp [Finset.mem_Ioc, not_le_of_gt hn]) h (-((σ : ℂ) + Complex.I*(t : ℂ)))
  rw [interval_dirichlet] at hp
  exact hp

theorem weighted_normalized_mean_square (s : Finset ℕ) (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N)
    (σ : ℝ) (hσ : 1 ≤ σ) (E : ℝ)
    (hE : (∑ n ∈ s, ‖a n‖^2 / (n : ℝ)^2) ≤ E)
    (A B : ℝ) (hAB : A ≤ B) :
    (∫ t in Icc A B, ‖verticalDirichlet152 s a σ t‖^2) ≤
      (B-A + 4*(N : ℝ)*(1+Real.log (N : ℝ))) * E := by
  have he : (∑ n ∈ s, ‖normalizedCoefficients152 a σ n‖^2) ≤ E := by
    apply le_trans _ hE
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (hs n hn).1
    have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
    have hden : (n : ℝ) ≤ (n : ℝ)^σ := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hσ
    have hnorm : ‖normalizedCoefficients152 a σ n‖ ≤ ‖a n‖/(n : ℝ) := by
      simp only [normalizedCoefficients152, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hn0.le σ)]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hn0 hden
    simpa only [div_pow] using pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hm := dirichlet_mean_square_le151 s
    (fun n => conj (normalizedCoefficients152 a σ n)) N hs A B
  simp only [RCLike.norm_conj] at hm
  have hc : 0 ≤ B-A + 4*(N : ℝ)*(1+Real.log (N : ℝ)) := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    have hba := sub_nonneg.mpr hAB
    positivity
  calc
    _ = ∫ t in A..B, ‖exponentialSum151 s
        (fun n => conj (normalizedCoefficients152 a σ n)) (fun n => Real.log n) t‖^2 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB]
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [verticalDirichlet_norm152 _ _ _ _ (by intro n hn; have := hs n hn; omega)]
    _ ≤ (B-A + 4*(N : ℝ)*(1+Real.log (N : ℝ))) *
        ∑ n ∈ s, ‖normalizedCoefficients152 a σ n‖^2 := hm
    _ ≤ _ := mul_le_mul_of_nonneg_left he hc

/-- An unconditional finite even-moment estimate. Its only coefficient
hypothesis is the actual pointwise Mangoldt majorant on the original interval. -/
theorem mangoldt_interval_even_moment (D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Finset.Ioc D N, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (h : ℕ) (σ : ℝ) (hσ : 1 ≤ σ) (A B : ℝ) (hAB : A ≤ B) :
    (∫ t in Icc A B, ‖verticalDirichlet152 (Finset.Ioc D N) a σ t‖^(2*h)) ≤
      (B-A + 4*((N^h : ℕ) : ℝ)*(1+Real.log ((N^h : ℕ) : ℝ))) *
      (((Real.log ((N^h : ℕ) : ℝ))^h / ((D^h : ℕ) : ℝ)) *
        (∑ n ∈ Finset.Ioc D N, ‖a n‖/(n : ℝ))^h) := by
  have he := interval_power_weighted_energy D N hD hDN a ha h
  have hm := weighted_normalized_mean_square (Finset.Ioc 0 (N^h))
    (fun n => (intervalCoefficients D N a ^ h) n) (N^h) (one_le_pow₀ (hD.trans hDN))
    (by intro n hn; have := Finset.mem_Ioc.mp hn; exact ⟨by omega,this.2⟩)
    σ hσ _ he A B hAB
  have hid (t : ℝ) :
      ‖verticalDirichlet152 (Finset.Ioc D N) a σ t‖^(2*h) =
      ‖verticalDirichlet152 (Finset.Ioc 0 (N^h))
        (fun n => (intervalCoefficients D N a ^ h) n) σ t‖^2 := by
    rw [← interval_vertical_power D N (hD.trans hDN) a h σ t, norm_pow,
      ← pow_mul, Nat.mul_comm h 2]
  simpa only [← hid] using hm

/-- All logarithmic losses in the finite moment estimate are explicit. -/
theorem mangoldt_interval_moment_log (D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Finset.Ioc D N, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (h : ℕ) (σ : ℝ) (hσ : 1 ≤ σ) (A B : ℝ) (hAB : A ≤ B)
    (R C X : ℝ) (hR : 1 ≤ R) (hC : 0 ≤ C) (hX : 2 ≤ X)
    (hN : (N : ℝ) ≤ R*(D : ℝ)) (hNX : (N : ℝ) ≤ X)
    (hT : B-A ≤ (D : ℝ)^h)
    (hMass : (∑ n ∈ Finset.Ioc D N, ‖a n‖/(n : ℝ)) ≤ C) :
    (∫ t in Icc A B, ‖verticalDirichlet152 (Finset.Ioc D N) a σ t‖^(2*h)) ≤
      C^h * (1+4*R^h) * ((h : ℝ)+1)^(h+1) * (1+Real.log X)^(h+1) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hR0 : 0 ≤ R := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hD.trans hDN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlogNX : Real.log (N : ℝ) ≤ Real.log X := Real.log_le_log hNp hNX
  have hlogpow : Real.log ((N^h : ℕ) : ℝ) = (h : ℝ)*Real.log (N : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hL : 0 ≤ Real.log ((N^h : ℕ) : ℝ) := by rw [hlogpow]; positivity
  have hW : 1 ≤ 1+Real.log ((N^h : ℕ) : ℝ) := by linarith
  have hWZ : 1+Real.log ((N^h : ℕ) : ℝ) ≤ ((h : ℝ)+1)*(1+Real.log X) := by
    rw [hlogpow]
    have ht := mul_le_mul_of_nonneg_left hlogNX (Nat.cast_nonneg h)
    nlinarith [Nat.cast_nonneg (α := ℝ) h]
  have hNZ : (N : ℝ)^h ≤ R^h*(D : ℝ)^h := by
    simpa only [mul_pow] using pow_le_pow_left₀ hNp.le hN h
  have hfactor : 0 ≤ 1+4*R^h := by positivity
  have hbracket : B-A + 4*((N^h : ℕ) : ℝ)*(1+Real.log ((N^h : ℕ) : ℝ)) ≤
      (D : ℝ)^h*(1+4*R^h)*(1+Real.log ((N^h : ℕ) : ℝ)) := by
    rw [Nat.cast_pow]
    have hWnonneg : 0 ≤ 1+Real.log ((N : ℝ)^h) := by
      simpa only [Nat.cast_pow] using (zero_le_one.trans hW)
    have hmain := mul_le_mul_of_nonneg_right hNZ
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hWnonneg)
    have htail := mul_le_mul_of_nonneg_left hW (pow_nonneg hDp.le h)
    simp only [Nat.cast_pow] at htail
    nlinarith
  have hMass0 : 0 ≤ ∑ n ∈ Finset.Ioc D N, ‖a n‖/(n : ℝ) :=
    Finset.sum_nonneg (fun n _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  have hm := mangoldt_interval_even_moment D N hD hDN a ha h σ hσ A B hAB
  have he :
      ((Real.log ((N^h : ℕ) : ℝ))^h / ((D^h : ℕ) : ℝ)) *
        (∑ n ∈ Finset.Ioc D N, ‖a n‖/(n : ℝ))^h ≤
      ((Real.log ((N^h : ℕ) : ℝ))^h / ((D^h : ℕ) : ℝ))*C^h :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMass0 hMass h)
      (div_nonneg (pow_nonneg hL h) (Nat.cast_nonneg _))
  have hbp : 0 ≤ (D : ℝ)^h*(1+4*R^h)*(1+Real.log ((N^h : ℕ) : ℝ)) := by positivity
  have he0 : 0 ≤ ((Real.log ((N^h : ℕ) : ℝ))^h / ((D^h : ℕ) : ℝ)) *
      (∑ n ∈ Finset.Ioc D N, ‖a n‖/(n : ℝ))^h := by positivity
  apply hm.trans
  calc
    _ ≤ ((D : ℝ)^h*(1+4*R^h)*(1+Real.log ((N^h : ℕ) : ℝ))) *
        (((Real.log ((N^h : ℕ) : ℝ))^h / ((D^h : ℕ) : ℝ))*C^h) :=
      mul_le_mul hbracket he he0 hbp
    _ = C^h*(1+4*R^h)*((1+Real.log ((N^h : ℕ) : ℝ))*
        (Real.log ((N^h : ℕ) : ℝ))^h) := by
      simp only [Nat.cast_pow]
      field_simp [hDp.ne']
    _ ≤ C^h*(1+4*R^h)*(1+Real.log ((N^h : ℕ) : ℝ))^(h+1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hL (by linarith : Real.log ((N^h : ℕ) : ℝ) ≤
          1+Real.log ((N^h : ℕ) : ℝ)) h) (by linarith)
    _ ≤ C^h*(1+4*R^h)*(((h : ℝ)+1)*(1+Real.log X))^(h+1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hWZ (h+1)) (by positivity)
    _ = _ := by rw [mul_pow]; ring


run_cmd do
  for target in [``finiteDirichlet_power_of_support, ``interval_dirichlet, ``interval_vertical_power, ``weighted_normalized_mean_square, ``mangoldt_interval_even_moment, ``mangoldt_interval_moment_log] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "MomentResidualEven PASSED; 6 declarations guarded"
end MomentResidualEven
end
