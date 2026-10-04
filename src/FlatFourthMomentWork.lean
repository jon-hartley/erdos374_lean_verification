import FlatSecondEnergyWork

/-! Explicit logarithmic fourth moment for arbitrary unit coefficients on an
integer interval. This supplies a flat-factor moment, not a prime cap. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace FlatFourthMomentWork
open MomentResidualInterval MomentResidualConvolution MomentResidualEven
open Erdos374.HarmanGram152

theorem weighted_energy (D N : ℕ) (hD : 1 ≤ D)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Finset.Ioc D N, ‖a n‖ ≤ 1) :
    (∑ n ∈ Finset.Ioc 0 (N^2), ‖(intervalCoefficients D N a ^ 2) n‖^2 / (n:ℝ)^2)
      ≤ ((N:ℝ)^2 * (1+Real.log ((N:ℝ)^2))^3) / (D:ℝ)^4 := by
  let f := intervalCoefficients D N a
  have hf : ∀ n, ‖f n‖ ≤ 1 := by
    intro n
    by_cases hn : n ∈ Finset.Ioc D N
    · simpa [f, hn] using ha n hn
    · simp [f, hn]
  have hpoint (n : ℕ) : ‖(f^2) n‖^2 / (n:ℝ)^2 ≤ ‖(f^2) n‖^2 / (D:ℝ)^4 := by
    by_cases hn : (f^2) n = 0
    · simp [hn]
    have hs := power_support f D N (by
      intro m hm
      have hh := intervalCoefficients_support D N a m hm
      exact ⟨hh.1.le, hh.2⟩) 2 n hn
    have hDR : (0:ℝ)<D := by exact_mod_cast (show 0<D by omega)
    have hb : (D:ℝ)^2 ≤ n := by exact_mod_cast hs.1
    have hb2 : (D:ℝ)^4 ≤ (n:ℝ)^2 := by
      have := pow_le_pow_left₀ (by positivity : 0 ≤ (D:ℝ)^2) hb 2
      simpa [←pow_mul] using this
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hb2
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 (N^2), ‖(f^2) n‖^2 / (D:ℝ)^4 :=
      Finset.sum_le_sum (fun n _ => hpoint n)
    _ = (∑ n ∈ Finset.Ioc 0 (N^2), ‖(f^2) n‖^2) / (D:ℝ)^4 := by
      rw [Finset.sum_div]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh := FlatSecondEnergyWork.second_energy f hf (N^2)
      norm_cast at hh ⊢

theorem fourth_moment (D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Finset.Ioc D N, ‖a n‖ ≤ 1)
    (σ A B : ℝ) (hσ : 1 ≤ σ) (hAB : A ≤ B) :
    (∫ t in Icc A B, ‖verticalDirichlet152 (Finset.Ioc D N) a σ t‖^4) ≤
      (B-A+4*(N:ℝ)^2*(1+Real.log ((N:ℝ)^2))) *
      (((N:ℝ)^2*(1+Real.log ((N:ℝ)^2))^3)/(D:ℝ)^4) := by
  have hm := weighted_normalized_mean_square (Finset.Ioc 0 (N^2))
    (fun n => (intervalCoefficients D N a ^ 2) n) (N^2)
    (one_le_pow₀ (hD.trans hDN))
    (by intro n hn; have := Finset.mem_Ioc.mp hn; exact ⟨by omega, this.2⟩)
    σ hσ _ (weighted_energy D N hD a ha) A B hAB
  have hid (t : ℝ) :
      ‖verticalDirichlet152 (Finset.Ioc D N) a σ t‖^4 =
      ‖verticalDirichlet152 (Finset.Ioc 0 (N^2))
        (fun n => (intervalCoefficients D N a ^ 2) n) σ t‖^2 := by
    rw [← interval_vertical_power D N (hD.trans hDN) a 2 σ t, norm_pow, ←pow_mul]
  simpa only [←hid, Nat.cast_pow] using hm

/-- Fixed-ratio intervals and time length at most D^2 have only log^4 cost. -/
theorem fourth_moment_log (D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Finset.Ioc D N, ‖a n‖ ≤ 1)
    (σ A B R : ℝ) (hσ : 1 ≤ σ) (hAB : A ≤ B)
    (hR : 1 ≤ R) (hN : (N:ℝ) ≤ R*D) (hT : B-A ≤ (D:ℝ)^2) :
    (∫ t in Icc A B, ‖verticalDirichlet152 (Finset.Ioc D N) a σ t‖^4) ≤
      (1+4*R^2)*R^2*(1+Real.log ((N:ℝ)^2))^4 := by
  have hDp : (0:ℝ)<D := by exact_mod_cast (show 0<D by omega)
  have hNp : (1:ℝ)≤N := by exact_mod_cast hD.trans hDN
  let L := 1+Real.log ((N:ℝ)^2)
  have hL : 1≤L := by
    have := Real.log_nonneg (one_le_pow₀ hNp (n := 2))
    dsimp [L]; linarith
  have hNL : (N:ℝ)^2 ≤ R^2*(D:ℝ)^2 := by
    simpa [mul_pow] using pow_le_pow_left₀ (by positivity : (0:ℝ)≤N) hN 2
  have hb : B-A+4*(N:ℝ)^2*L ≤ (D:ℝ)^2*(1+4*R^2)*L := by
    have hh := mul_le_mul_of_nonneg_right hNL (by positivity : 0≤4*L)
    have hh2 := mul_le_mul_of_nonneg_left hL (by positivity : 0≤(D:ℝ)^2)
    nlinarith
  have he : ((N:ℝ)^2*L^3)/(D:ℝ)^4 ≤
      (R^2*(D:ℝ)^2*L^3)/(D:ℝ)^4 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hNL (by positivity)) (by positivity)
  apply (fourth_moment D N hD hDN a ha σ A B hσ hAB).trans
  change (B-A+4*(N:ℝ)^2*L)*(((N:ℝ)^2*L^3)/(D:ℝ)^4) ≤ _
  calc
    _ ≤ ((D:ℝ)^2*(1+4*R^2)*L)*((R^2*(D:ℝ)^2*L^3)/(D:ℝ)^4) :=
      mul_le_mul hb he (by positivity) (by positivity)
    _ = _ := by
      change _ = (1+4*R^2)*R^2*L^4
      field_simp [hDp.ne']

run_cmd do
  for decl in [``weighted_energy, ``fourth_moment, ``fourth_moment_log] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end FlatFourthMomentWork
