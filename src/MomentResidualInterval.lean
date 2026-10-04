import MomentResidualConvolution

/-! Fresh proof adaptation of the retained 162 reference source. All imports belong
to the current verified closure or to this new branch; no old object is used.
Actual von Mangoldt coefficients include all prime powers. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators ComplexConjugate
open Set Filter MeasureTheory
namespace MomentResidualInterval
open MomentResidualConvolution
/-- The coefficient estimate for any genuinely finite Mangoldt-dominated array,
including a long fixed-ratio interval rather than only a dyadic interval. -/
theorem power_weighted_energy_of_support (a : ArithmeticFunction ℂ)
    (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N)
    (hs : ∀ n, a n ≠ 0 → D ≤ n ∧ n ≤ N) (h : ℕ) :
    (∑ n ∈ Finset.Ioc 0 (N^h), ‖(a^h) n‖^2 / (n : ℝ)^2) ≤
      ((Real.log ((N^h : ℕ) : ℝ))^h / ((D^h : ℕ) : ℝ)) *
        (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ / (n : ℝ))^h := by
  have hDh : 1 ≤ D^h := one_le_pow₀ hD
  have hNh : 1 ≤ N^h := one_le_pow₀ (hD.trans hDN)
  have hsubset : Finset.Icc (D^h) (N^h) ⊆ Finset.Ioc 0 (N^h) := by
    intro n hn
    have hb := Finset.mem_Icc.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega, hb.2⟩
  have heq : (∑ n ∈ Finset.Ioc 0 (N^h), ‖(a^h) n‖^2 / (n : ℝ)^2) =
      ∑ n ∈ Finset.Icc (D^h) (N^h), ‖(a^h) n‖^2 / (n : ℝ)^2 := by
    symm
    apply Finset.sum_subset hsubset
    intro n hn hnot
    have hz : (a^h) n = 0 := by
      by_contra hne
      exact hnot (Finset.mem_Icc.mpr (power_support a D N hs h n hne))
    simp [hz]
  rw [heq]
  apply (weighted_power_energy_le_mass a ha h (D^h) (N^h) hDh
    (Finset.Icc (D^h) (N^h)) (by intro n hn; exact Finset.mem_Icc.mp hn)).trans
  apply mul_le_mul_of_nonneg_left
  · calc
      _ ≤ ∑ n ∈ Finset.Ioc 0 (N^h), ‖(a^h) n‖ / (n : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intros; positivity
      _ ≤ _ := power_reciprocal_mass_le a N (hD.trans hDN)
        (by intro n hn; by_contra hne; exact (not_lt_of_ge (hs n hne).2) hn) h
  · exact div_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast hNh)) h)
      (Nat.cast_nonneg _)

def intervalCoefficients (D N : ℕ) (a : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ∈ Finset.Ioc D N then a n else 0, by simp⟩

@[simp] theorem intervalCoefficients_apply (D N : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    intervalCoefficients D N a n = if n ∈ Finset.Ioc D N then a n else 0 := rfl

theorem intervalCoefficients_support (D N : ℕ) (a : ℕ → ℂ) (n : ℕ)
    (hn : intervalCoefficients D N a n ≠ 0) : D < n ∧ n ≤ N := by
  by_cases hmem : n ∈ Finset.Ioc D N
  · exact Finset.mem_Ioc.mp hmem
  · simp [hmem] at hn

theorem intervalCoefficients_mangoldt_bound (D N : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Finset.Ioc D N, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n) (n : ℕ) :
    ‖intervalCoefficients D N a n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  by_cases hn : n ∈ Finset.Ioc D N
  · simpa [hn] using ha n hn
  · simp [hn]

theorem interval_reciprocal_mass (D N : ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc 0 N, ‖intervalCoefficients D N a n‖ / (n : ℝ)) =
      ∑ n ∈ Finset.Ioc D N, ‖a n‖ / (n : ℝ) := by
  calc
    _ = ∑ n ∈ Finset.Ioc D N, ‖intervalCoefficients D N a n‖ / (n : ℝ) := by
      symm
      apply Finset.sum_subset (Finset.Ioc_subset_Ioc (Nat.zero_le _) le_rfl)
      intro n hn hnot
      simp [hnot]
    _ = _ := Finset.sum_congr rfl (by intro n hn; simp [hn])

theorem interval_power_weighted_energy (D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Finset.Ioc D N, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (h : ℕ) :
    (∑ n ∈ Finset.Ioc 0 (N^h), ‖(intervalCoefficients D N a ^ h) n‖^2 / (n : ℝ)^2) ≤
      ((Real.log ((N^h : ℕ) : ℝ))^h / ((D^h : ℕ) : ℝ)) *
        (∑ n ∈ Finset.Ioc D N, ‖a n‖ / (n : ℝ))^h := by
  have hh := power_weighted_energy_of_support (intervalCoefficients D N a)
    (intervalCoefficients_mangoldt_bound D N a ha) D N hD hDN
    (by intro n hn; have := intervalCoefficients_support D N a n hn; exact ⟨this.1.le,this.2⟩) h
  simpa only [interval_reciprocal_mass] using hh

def cpowTwist (f : ArithmeticFunction ℂ) (z : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => f n * (n : ℂ) ^ z, by simp⟩

@[simp] theorem cpowTwist_apply (f : ArithmeticFunction ℂ) (z : ℂ) (n : ℕ) :
    cpowTwist f z n = f n * (n : ℂ) ^ z := rfl

theorem cpowTwist_mul (f g : ArithmeticFunction ℂ) (z : ℂ) :
    cpowTwist (f * g) z = cpowTwist f z * cpowTwist g z := by
  ext n
  simp only [cpowTwist_apply, ArithmeticFunction.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← hp', Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

theorem finite_convolution_sum (N M : ℕ) (_hN : 1 ≤ N) (hM : 1 ≤ M)
    (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, N < n → f n = 0) (hg : ∀ n, M < n → g n = 0) :
    (∑ n ∈ Finset.Ioc 0 (N * M), (f * g) n) =
      (∑ n ∈ Finset.Ioc 0 N, f n) * (∑ n ∈ Finset.Ioc 0 M, g n) := by
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  have hNM : N ≤ N * M := by nlinarith
  calc
    _ = ∑ d ∈ Finset.Ioc 0 N, f d * ∑ m ∈ Finset.Ioc 0 (N * M / d), g m := by
      symm
      apply Finset.sum_subset (Finset.Ioc_subset_Ioc le_rfl hNM)
      intro d hd hnot
      have hd0 := (Finset.mem_Ioc.mp hd).1
      have hdN : N < d := by simpa [Finset.mem_Ioc, hd0] using hnot
      rw [hf d hdN, zero_mul]
    _ = ∑ d ∈ Finset.Ioc 0 N, f d * ∑ m ∈ Finset.Ioc 0 M, g m := by
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      have hd0 := (Finset.mem_Ioc.mp hd).1
      have hdN := (Finset.mem_Ioc.mp hd).2
      have hMd : M ≤ N * M / d := (Nat.le_div_iff_mul_le hd0).mpr (by nlinarith)
      symm
      apply Finset.sum_subset (Finset.Ioc_subset_Ioc le_rfl hMd)
      intro m hm hnot
      have hm0 := (Finset.mem_Ioc.mp hm).1
      apply hg
      simpa [Finset.mem_Ioc, hm0] using hnot
    _ = _ := by rw [Finset.sum_mul]

def finiteDirichlet (N : ℕ) (f : ArithmeticFunction ℂ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, f n * (n : ℂ) ^ z

theorem finiteDirichlet_mul (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, N < n → f n = 0) (hg : ∀ n, M < n → g n = 0) (z : ℂ) :
    finiteDirichlet (N * M) (f * g) z =
      finiteDirichlet N f z * finiteDirichlet M g z := by
  change (∑ n ∈ Finset.Ioc 0 (N * M), cpowTwist (f * g) z n) = _
  rw [cpowTwist_mul]
  exact finite_convolution_sum N M hN hM (cpowTwist f z) (cpowTwist g z)
    (by intro n hn; simp [hf n hn]) (by intro n hn; simp [hg n hn])


run_cmd do
  for target in [``power_weighted_energy_of_support, ``intervalCoefficients, ``intervalCoefficients_apply, ``intervalCoefficients_support, ``intervalCoefficients_mangoldt_bound, ``interval_reciprocal_mass, ``interval_power_weighted_energy, ``cpowTwist, ``cpowTwist_apply, ``cpowTwist_mul, ``finite_convolution_sum, ``finiteDirichlet, ``finiteDirichlet_mul] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "MomentResidualInterval PASSED; 13 declarations guarded"
end MomentResidualInterval
end
