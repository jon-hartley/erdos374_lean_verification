import FlatDivisorEnergyWork

/-! Explicit logarithmic eighth moment for arbitrary unit coefficients on an
integer interval. This supplies a flat-factor moment, not a prime cap. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace FlatEighthMomentWork
open MomentResidualInterval MomentResidualConvolution MomentResidualEven
open Erdos374.HarmanGram152

theorem weighted_energy (D N : ℕ) (hD : 1 ≤ D)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Finset.Ioc D N, ‖a n‖ ≤ 1) :
    (∑ n ∈ Finset.Ioc 0 (N^4), ‖(intervalCoefficients D N a ^ 4) n‖^2 / (n:ℝ)^2)
      ≤ ((N:ℝ)^4 * (1+Real.log ((N:ℝ)^4))^15) / (D:ℝ)^8 := by
  let f := intervalCoefficients D N a
  have hf : ∀ n, ‖f n‖ ≤ 1 := by
    intro n
    by_cases hn : n ∈ Finset.Ioc D N
    · simpa [f, hn] using ha n hn
    · simp [f, hn]
  have hpoint (n : ℕ) : ‖(f^4) n‖^2 / (n:ℝ)^2 ≤ ‖(f^4) n‖^2 / (D:ℝ)^8 := by
    by_cases hn : (f^4) n = 0
    · simp [hn]
    have hs := power_support f D N (by
      intro m hm
      have hh := intervalCoefficients_support D N a m hm
      exact ⟨hh.1.le, hh.2⟩) 4 n hn
    have hDR : (0:ℝ)<D := by exact_mod_cast (show 0<D by omega)
    have hb : (D:ℝ)^4 ≤ n := by exact_mod_cast hs.1
    have hb2 : (D:ℝ)^8 ≤ (n:ℝ)^2 := by
      have := pow_le_pow_left₀ (by positivity : 0 ≤ (D:ℝ)^4) hb 2
      simpa [←pow_mul] using this
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hb2
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 (N^4), ‖(f^4) n‖^2 / (D:ℝ)^8 :=
      Finset.sum_le_sum (fun n _ => hpoint n)
    _ = (∑ n ∈ Finset.Ioc 0 (N^4), ‖(f^4) n‖^2) / (D:ℝ)^8 := by
      rw [Finset.sum_div]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh := FlatDivisorEnergyWork.fourth_energy f hf (N^4)
      norm_cast at hh ⊢

theorem eighth_moment (D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Finset.Ioc D N, ‖a n‖ ≤ 1)
    (σ A B : ℝ) (hσ : 1 ≤ σ) (hAB : A ≤ B) :
    (∫ t in Icc A B, ‖verticalDirichlet152 (Finset.Ioc D N) a σ t‖^8) ≤
      (B-A+4*(N:ℝ)^4*(1+Real.log ((N:ℝ)^4))) *
      (((N:ℝ)^4*(1+Real.log ((N:ℝ)^4))^15)/(D:ℝ)^8) := by
  have hm := weighted_normalized_mean_square (Finset.Ioc 0 (N^4))
    (fun n => (intervalCoefficients D N a ^ 4) n) (N^4)
    (one_le_pow₀ (hD.trans hDN))
    (by intro n hn; have := Finset.mem_Ioc.mp hn; exact ⟨by omega, this.2⟩)
    σ hσ _ (weighted_energy D N hD a ha) A B hAB
  have hid (t : ℝ) :
      ‖verticalDirichlet152 (Finset.Ioc D N) a σ t‖^8 =
      ‖verticalDirichlet152 (Finset.Ioc 0 (N^4))
        (fun n => (intervalCoefficients D N a ^ 4) n) σ t‖^2 := by
    rw [← interval_vertical_power D N (hD.trans hDN) a 4 σ t, norm_pow, ←pow_mul]
  simpa only [←hid, Nat.cast_pow] using hm

/-- Fixed-ratio intervals and time length at most D^4 have only log^16 cost. -/
theorem eighth_moment_log (D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Finset.Ioc D N, ‖a n‖ ≤ 1)
    (σ A B R : ℝ) (hσ : 1 ≤ σ) (hAB : A ≤ B)
    (hR : 1 ≤ R) (hN : (N:ℝ) ≤ R*D) (hT : B-A ≤ (D:ℝ)^4) :
    (∫ t in Icc A B, ‖verticalDirichlet152 (Finset.Ioc D N) a σ t‖^8) ≤
      (1+4*R^4)*R^4*(1+Real.log ((N:ℝ)^4))^16 := by
  have hDp : (0:ℝ)<D := by exact_mod_cast (show 0<D by omega)
  have hNp : (1:ℝ)≤N := by exact_mod_cast hD.trans hDN
  let L := 1+Real.log ((N:ℝ)^4)
  have hL : 1≤L := by
    have := Real.log_nonneg (one_le_pow₀ hNp (n := 4))
    dsimp [L]; linarith
  have hNL : (N:ℝ)^4 ≤ R^4*(D:ℝ)^4 := by
    simpa [mul_pow] using pow_le_pow_left₀ (by positivity : (0:ℝ)≤N) hN 4
  have hb : B-A+4*(N:ℝ)^4*L ≤ (D:ℝ)^4*(1+4*R^4)*L := by
    have hh := mul_le_mul_of_nonneg_right hNL (by positivity : 0≤4*L)
    have hh2 := mul_le_mul_of_nonneg_left hL (by positivity : 0≤(D:ℝ)^4)
    nlinarith
  have he : ((N:ℝ)^4*L^15)/(D:ℝ)^8 ≤
      (R^4*(D:ℝ)^4*L^15)/(D:ℝ)^8 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hNL (by positivity)) (by positivity)
  apply (eighth_moment D N hD hDN a ha σ A B hσ hAB).trans
  change (B-A+4*(N:ℝ)^4*L)*(((N:ℝ)^4*L^15)/(D:ℝ)^8) ≤ _
  calc
    _ ≤ ((D:ℝ)^4*(1+4*R^4)*L)*((R^4*(D:ℝ)^4*L^15)/(D:ℝ)^8) :=
      mul_le_mul hb he (by positivity) (by positivity)
    _ = _ := by
      change _ = (1+4*R^4)*R^4*L^16
      field_simp [hDp.ne']

theorem dyadic_eighth_moment (D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N)
    (hN : N ≤ 2*D) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Finset.Ioc D N, ‖a n‖ ≤ 1)
    (σ A B : ℝ) (hσ : 1 ≤ σ) (hAB : A ≤ B) (hT : B-A ≤ (D:ℝ)^4) :
    (∫ t in Icc A B, ‖verticalDirichlet152 (Finset.Ioc D N) a σ t‖^8) ≤
      1040*(1+4*Real.log (N:ℝ))^16 := by
  have hm := eighth_moment_log D N hD hDN a ha σ A B 2 hσ hAB
    (by norm_num) (by exact_mod_cast hN) hT
  simpa only [Real.log_pow, Nat.cast_ofNat, show (1+4*(2:ℝ)^4)*2^4=1040 by norm_num]
    using hm

run_cmd do
  for decl in [``weighted_energy, ``eighth_moment, ``eighth_moment_log, ``dyadic_eighth_moment] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end FlatEighthMomentWork
