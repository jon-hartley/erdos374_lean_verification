import CompactIntegral

/-! A first-order Euler estimate for the actual flat Dirichlet polynomial. -/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace FlatCofactorApproximation
open Erdos374.HarmanGram152

theorem real_power_bound (K n : ℕ) (σ : ℝ)
    (hK : 1 ≤ K) (hKn : K ≤ n) (hσ : 1 ≤ σ) :
    (n : ℝ) ^ (-σ) ≤ (K : ℝ)⁻¹ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hKnR : (K : ℝ) ≤ n := by exact_mod_cast hKn
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  calc
    (n : ℝ) ^ (-σ) ≤ (K : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hKnR (by linarith)
    _ ≤ (K : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hKR (by linarith)
    _ = _ := Real.rpow_neg_one _

theorem inverse_power_bound (K n : ℕ) (σ : ℝ) (s : ℂ)
    (hK : 1 ≤ K) (hKn : K ≤ n) (hσ : 1 ≤ σ)
    (hsre : s.re = σ) :
    ‖(n : ℂ) ^ (-s)‖ ≤ (K : ℝ)⁻¹ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [← Complex.ofReal_natCast n, Complex.norm_cpow_eq_rpow_re_of_pos hn]
  simp only [Complex.neg_re, hsre]
  exact real_power_bound K n σ hK hKn hσ

theorem bound_any_upper (K lo hi : ℕ) (σ t : ℝ)
    (hK : 1 ≤ K) (hlo : K ≤ lo) (hhi : lo < hi)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) :
    ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t -
      (((hi : ℂ) ^ (1 - ((σ : ℂ) + Complex.I * (t : ℂ))) -
        (lo : ℂ) ^ (1 - ((σ : ℂ) + Complex.I * (t : ℂ)))) /
          (1 - ((σ : ℂ) + Complex.I * (t : ℂ))))‖ ≤
      (3 + |t|) / (K : ℝ) := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hsre : s.re = σ := by simp [s]
  have hsone : s ≠ 1 := by
    intro heq
    have hh := congrArg Complex.re heq
    simp only [hsre, Complex.one_re] at hh
    linarith
  have hszero : s ≠ 0 := by
    intro heq
    have hh := congrArg Complex.re heq
    simp only [hsre, Complex.zero_re] at hh
    linarith
  have hpos : lo ∈ Ioo 0 hi := ⟨by omega, hhi⟩
  have heq : verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t =
      ∑ n ∈ Finset.Ioc lo hi, 1 / (n : ℂ) ^ s := by
    unfold verticalDirichlet152
    apply Finset.sum_congr rfl
    intro n hn
    simp only [one_mul, one_div]
    change (n : ℂ) ^ (-s) = ((n : ℂ) ^ s)⁻¹
    exact Complex.cpow_neg _ _
  have hformula := ZetaSum_aux1 (a := lo) (b := hi)
    (s := s) hsone hszero hpos
  rw [← heq] at hformula
  have hnormint :
      ‖∫ x in (lo : ℝ)..(hi : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))‖ ≤
        ((lo : ℝ) ^ (-σ) - (hi : ℝ) ^ (-σ)) / σ := by
    calc
      _ ≤ ∫ x in (lo : ℝ)..(hi : ℝ),
          ‖(⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by exact_mod_cast hhi.le)
      _ = ∫ x in (lo : ℝ)..(hi : ℝ),
          ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp only [div_eq_mul_inv, ← Complex.cpow_neg]
      _ ≤ _ := by
        simpa only [hsre] using
          (ZetaBnd_aux1a (a := (lo : ℝ)) (b := (hi : ℝ))
            (s := s) (by exact_mod_cast (show 0 < lo by omega))
            (by exact_mod_cast hhi) (by linarith))
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hlong : ((lo : ℝ) ^ (-σ) - (hi : ℝ) ^ (-σ)) / σ ≤ (K : ℝ)⁻¹ := by
    have hloPow : (lo : ℝ) ^ (-σ) ≤ (K : ℝ)⁻¹ := by
      exact real_power_bound K lo σ hK hlo hσ.le
    have hhiPow : 0 ≤ (hi : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
    have hloPowNonneg : 0 ≤ (lo : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hloPow (by linarith : 0 ≤ σ)]
  have hsbound : ‖s‖ ≤ 2 + |t| := by
    calc
      _ ≤ ‖(σ : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ := norm_add_le _ _
      _ = σ + |t| := by
        simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : 0 ≤ σ), one_mul]
      _ ≤ _ := by linarith
  have hendlo : ‖1 / (lo : ℂ) ^ s‖ ≤ (K : ℝ)⁻¹ := by
    rw [one_div, ← Complex.cpow_neg]
    exact inverse_power_bound K lo σ s hK hlo hσ.le hsre
  have hendhi : ‖1 / (hi : ℂ) ^ s‖ ≤ (K : ℝ)⁻¹ := by
    rw [one_div, ← Complex.cpow_neg]
    exact inverse_power_bound K hi σ s hK (by omega) hσ.le hsre
  have hident : verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t -
      ((hi : ℂ) ^ (1 - s) - (lo : ℂ) ^ (1 - s)) / (1 - s) =
      1 / 2 * (1 / (hi : ℂ) ^ s) -
      1 / 2 * (1 / (lo : ℂ) ^ s) +
      s * ∫ x in (lo : ℝ)..(hi : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
    rw [hformula]
    ring
  change ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t -
    ((hi : ℂ) ^ (1 - s) - (lo : ℂ) ^ (1 - s)) / (1 - s)‖ ≤ _
  rw [hident]
  have hh := norm_add_le
    (1 / 2 * (1 / (hi : ℂ) ^ s) - 1 / 2 * (1 / (lo : ℂ) ^ s))
    (s * ∫ x in (lo : ℝ)..(hi : ℝ),
      (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  have hendpoint : ‖1 / 2 * (1 / (hi : ℂ) ^ s) -
      1 / 2 * (1 / (lo : ℂ) ^ s)‖ ≤ (K : ℝ)⁻¹ := by
    calc
      _ ≤ ‖(1 / 2 : ℂ) * (1 / (hi : ℂ) ^ s)‖ +
          ‖(1 / 2 : ℂ) * (1 / (lo : ℂ) ^ s)‖ := norm_sub_le _ _
      _ = (1 / 2 : ℝ) * ‖1 / (hi : ℂ) ^ s‖ +
          (1 / 2 : ℝ) * ‖1 / (lo : ℂ) ^ s‖ := by norm_num [norm_mul]
      _ ≤ (1 / 2 : ℝ) * (K : ℝ)⁻¹ +
          (1 / 2 : ℝ) * (K : ℝ)⁻¹ := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (K : ℝ)⁻¹ + (2 + |t|) * (K : ℝ)⁻¹ := by
      apply hh.trans
      rw [norm_mul]
      exact add_le_add hendpoint
        (mul_le_mul hsbound (hnormint.trans hlong) (norm_nonneg _) (by positivity))
    _ = (3 + |t|) / (K : ℝ) := by field_simp; ring

theorem bound (K lo hi : ℕ) (σ t : ℝ)
    (hK : 1 ≤ K) (hlo : K ≤ lo) (hhi : lo < hi)
    (_hhiK : hi ≤ 2 * K) (hσ : 1 < σ) (hσtwo : σ ≤ 2) :
    ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t -
      (((hi : ℂ) ^ (1 - ((σ : ℂ) + Complex.I * (t : ℂ))) -
        (lo : ℂ) ^ (1 - ((σ : ℂ) + Complex.I * (t : ℂ)))) /
          (1 - ((σ : ℂ) + Complex.I * (t : ℂ))))‖ ≤
      (3 + |t|) / (K : ℝ) :=
  bound_any_upper K lo hi σ t hK hlo hhi hσ hσtwo

end FlatCofactorApproximation

#print axioms FlatCofactorApproximation.bound
run_cmd do
  for target in [``FlatCofactorApproximation.bound_any_upper,
      ``FlatCofactorApproximation.bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FLAT COFACTOR APPROXIMATION PASSED"
