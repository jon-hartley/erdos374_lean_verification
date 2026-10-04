import Erdos374_Update152

/-! Fresh namespace port of the proved HarmanMangoldtMass161 source.
Only the import is changed to the currently rebuilt Update152 seed containing
the same WeightedPrimeSampling151 helpers and closed psiMediumPNT. No old
work/build object is imported. Actual reciprocal mass follows from that PNT. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Erdos374.PositiveInteriorMass
open WeightedPrimeSampling151 RemainingAnalytic115.RemainingAnalytic141

def mangoldtComplex (n : ℕ) : ℂ := ArithmeticFunction.vonMangoldt n

def reciprocalMangoldtMass (N : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)

lemma mangoldtComplex_sum (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, mangoldtComplex n = (Chebyshev.psi x : ℂ) := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp [mangoldtComplex, Chebyshev.psi, Complex.ofReal_sum]

theorem weighted_psi_abel {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {g g' : ℝ → ℂ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hc : ContinuousOn g' (Icc a b)) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g n * mangoldtComplex n =
      g b * (Chebyshev.psi b : ℂ) - g a * (Chebyshev.psi a : ℂ) -
        ∫ t in a..b, g' t * (Chebyshev.psi t : ℂ) := by
  have h := sum_mul_eq_sub_sub_integral_mul mangoldtComplex ha hab
    (fun t ht => (hd t ht).differentiableAt) (deriv_integrableOn hd hc)
  simp_rw [mangoldtComplex_sum] at h
  rw [← intervalIntegral.integral_of_le hab] at h
  convert h using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [(hd t (by simpa only [uIcc_of_le hab] using ht)).deriv]

lemma weighted_psi_kernel_integrable {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {g' : ℝ → ℂ} (hc : ContinuousOn g' (Icc a b)) :
    IntervalIntegrable (fun t => g' t * (Chebyshev.psi t : ℂ)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have h := integrableOn_mul_sum_Icc mangoldtComplex (m := 0) ha hc.integrableOn_Icc
  simpa only [mangoldtComplex_sum] using h

theorem weighted_psi_discrepancy_le {a b R : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (_hR : 0 ≤ R) {g g' : ℝ → ℂ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hc : ContinuousOn g' (Icc a b))
    (hψ : ∀ t ∈ Icc a b, |Chebyshev.psi t - t| ≤ R) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g n * mangoldtComplex n) -
      (∫ t in a..b, g t)‖ ≤
      R * (‖g a‖ + ‖g b‖ + ∫ t in a..b, ‖g' t‖) := by
  have hti : IntervalIntegrable (fun t => g' t * (t : ℂ)) volume a b :=
    (hc.mul Complex.continuous_ofReal.continuousOn).intervalIntegrable_of_Icc hab
  have he : (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g n * mangoldtComplex n) -
      (∫ t in a..b, g t) =
      g b * ((Chebyshev.psi b - b : ℝ) : ℂ) -
        g a * ((Chebyshev.psi a - a : ℝ) : ℂ) -
          ∫ t in a..b, g' t * ((Chebyshev.psi t - t : ℝ) : ℂ) := by
    rw [weighted_psi_abel ha hab hd hc, weighted_identity_integral hab hd hc]
    simp only [Complex.ofReal_sub, mul_sub]
    rw [intervalIntegral.integral_sub (weighted_psi_kernel_integrable ha hab hc) hti]
    ring
  have hi : ‖∫ t in a..b, g' t * ((Chebyshev.psi t - t : ℝ) : ℂ)‖ ≤
      (∫ t in a..b, ‖g' t‖) * R := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · apply Eventually.of_forall
      intro t ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hψ t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)
    · exact (hc.norm.intervalIntegrable_of_Icc hab).mul_const R
  have hend (t : ℝ) (ht : t ∈ Icc a b) :
      ‖g t * ((Chebyshev.psi t - t : ℝ) : ℂ)‖ ≤ ‖g t‖ * R := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hψ t ht) (norm_nonneg _)
  rw [he]
  calc
    _ ≤ (‖g b * ((Chebyshev.psi b - b : ℝ) : ℂ)‖ +
          ‖g a * ((Chebyshev.psi a - a : ℝ) : ℂ)‖) +
          ‖∫ t in a..b, g' t * ((Chebyshev.psi t - t : ℝ) : ℂ)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (‖g b‖ * R + ‖g a‖ * R) + (∫ t in a..b, ‖g' t‖) * R :=
      add_le_add (add_le_add (hend b ⟨hab, le_rfl⟩) (hend a ⟨le_rfl, hab⟩)) hi
    _ = _ := by ring

theorem psi_error_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ ε * x := by
  obtain ⟨c, hc, hPNT⟩ := ExternalInputs149.psiMediumPNT
  obtain ⟨C, hC, hb⟩ := Asymptotics.isBigO_iff'.mp hPNT
  have hw := medium_logPower_eventually_small141 0 c hc (ε / C) (by positivity)
  filter_upwards [hb, hw, eventually_ge_atTop (1 : ℝ)] with x hx hxw hx1
  have hx0 : 0 ≤ x := by linarith
  have he0 : 0 ≤ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by positivity
  have he : |Chebyshev.psi x - x| ≤
      C * (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg he0] using hx
  have hsmall : C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) ≤ ε := by
    have hh := mul_le_mul_of_nonneg_left hxw.le hC.le
    simpa only [pow_zero, mul_one, mul_div_cancel₀ _ (ne_of_gt hC)] using hh
  calc
    _ ≤ _ := he
    _ = x * (C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := by ring
    _ ≤ x * ε := mul_le_mul_of_nonneg_left hsmall hx0
    _ = _ := by ring

theorem reciprocal_mass_discrepancy (N ε : ℝ) (hN : 0 < N) (hε : 0 ≤ ε)
    (hψ : ∀ t ∈ Icc N (2*N), |Chebyshev.psi t - t| ≤ ε * t) :
    |reciprocalMangoldtMass N - Real.log 2| ≤ 6 * ε := by
  have hab : N ≤ 2 * N := by linarith
  let g : ℝ → ℂ := fun t => (t : ℂ)⁻¹
  let gd : ℝ → ℂ := fun t => -((t : ℂ)^2)⁻¹
  have hd : ∀ t ∈ Icc N (2*N), HasDerivAt g (gd t) t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hN.trans_le ht.1))
    simpa [g, gd, div_eq_mul_inv] using! (Complex.hasDerivAt_ofReal t).inv ht0
  have hc : ContinuousOn gd (Icc N (2*N)) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hN.trans_le ht.1))
    have hco : ContinuousAt (fun x : ℝ => (x : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt
    exact ((hco.pow 2).inv₀ (pow_ne_zero 2 ht0)).neg.continuousWithinAt
  have hgnorm (t : ℝ) (ht : 0 < t) : ‖g t‖ = 1 / t := by
    simp [g, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, one_div]
  have hdgnorm (t : ℝ) (ht : 0 < t) : ‖gd t‖ = 1 / t^2 := by
    simp [gd, norm_inv, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, one_div]
  have hv : (∫ t in N..(2*N), ‖gd t‖) ≤ 1 / N := by
    calc
      _ ≤ ∫ t in N..(2*N), 1 / N^2 := by
        apply intervalIntegral.integral_mono_on hab (hc.norm.intervalIntegrable_of_Icc hab)
          intervalIntegrable_const
        intro t ht
        rw [hdgnorm t (hN.trans_le ht.1)]
        exact one_div_le_one_div_of_le (sq_pos_of_pos hN)
          (pow_le_pow_left₀ hN.le ht.1 2)
      _ = _ := by rw [intervalIntegral.integral_const]; simp; field_simp; ring
  have hb := weighted_psi_discrepancy_le hN.le hab (by positivity : 0 ≤ 2*ε*N)
    hd hc (by intro t ht; exact (hψ t ht).trans (by nlinarith [ht.2]))
  have heSum : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊, g n * mangoldtComplex n) =
      (reciprocalMangoldtMass N : ℂ) := by
    simp only [reciprocalMangoldtMass, Complex.ofReal_sum, Complex.ofReal_div]
    apply Finset.sum_congr rfl
    intro n hn
    simp [g, mangoldtComplex, div_eq_mul_inv, mul_comm]
  have heInt : (∫ t in N..(2*N), g t) = (Real.log 2 : ℂ) := by
    simp only [g, ← Complex.ofReal_inv, intervalIntegral.integral_ofReal]
    rw [integral_inv_of_pos hN (by positivity)]
    congr 2
    field_simp
  rw [heSum, heInt, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hb
  refine hb.trans ?_
  rw [hgnorm N hN, hgnorm (2*N) (by positivity)]
  have hhalf : 1 / (2*N) ≤ 1 / N := one_div_le_one_div_of_le hN hab
  calc
    _ ≤ (2*ε*N) * (1/N + 1/N + 1/N) := by gcongr
    _ = 6*ε := by field_simp; ring

theorem reciprocal_mass_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop, |reciprocalMangoldtMass N - Real.log 2| ≤ ε := by
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (psi_error_eventually (ε/6) (by positivity))
  refine eventually_atTop.mpr ⟨max 1 Y, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNY : Y ≤ N := (le_max_right _ _).trans hN
  have hh := reciprocal_mass_discrepancy N (ε/6) (by linarith) (by positivity)
    (by intro t ht; exact hY t (hNY.trans ht.1))
  convert hh using 1; ring

theorem reciprocal_mass_bounds :
    ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N ≥ N0,
      (999/1000 : ℝ) * Real.log 2 ≤ reciprocalMangoldtMass N ∧
      reciprocalMangoldtMass N ≤ (1001/1000 : ℝ) * Real.log 2 := by
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (reciprocal_mass_eventually (Real.log 2 / 1000) (by positivity))
  refine ⟨max 1 Y, le_max_left _ _, ?_⟩
  intro N hN
  have hh := abs_le.mp (hY N ((le_max_right _ _).trans hN))
  constructor <;> linarith

#print axioms reciprocal_mass_bounds
run_cmd do
  for target in [``mangoldtComplex_sum, ``weighted_psi_abel,
      ``weighted_psi_kernel_integrable, ``weighted_psi_discrepancy_le,
      ``psi_error_eventually, ``reciprocal_mass_discrepancy,
      ``reciprocal_mass_eventually, ``reciprocal_mass_bounds] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
end Erdos374.PositiveInteriorMass
end
