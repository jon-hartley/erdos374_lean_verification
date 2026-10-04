import PositiveInteriorMass

/-! Fresh proof adaptation of the retained 162 reference source. All imports belong
to the current verified closure or to this new branch; no old object is used.
Actual von Mangoldt coefficients include all prime powers. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators ComplexConjugate
open Set Filter MeasureTheory
namespace MomentResidualConvolution

/-- A bounded complex coefficient array may be convolved without a divisor-square
loss: the von Mangoldt divisor identity controls its pointwise magnitude. -/
theorem convolution_power_log_bound (a : ArithmeticFunction ℂ)
    (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n) (h n : ℕ) :
    ‖(a^h) n‖ ≤ (Real.log (n : ℝ))^h := by
  induction h generalizing n with
  | zero =>
    by_cases hn : n = 1 <;> simp [hn]
  | succ h ih =>
    by_cases hn : n = 0
    · simp [hn]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    rw [pow_succ', ArithmeticFunction.mul_apply]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ p ∈ n.divisorsAntidiagonal,
          ArithmeticFunction.vonMangoldt p.1 * (Real.log (n : ℝ))^h := by
        apply Finset.sum_le_sum
        intro p hp
        have hp1 : 1 ≤ p.1 := Nat.one_le_iff_ne_zero.mpr
          (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)
        have hp2 : 1 ≤ p.2 := Nat.one_le_iff_ne_zero.mpr
          (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp)
        have hp2n : p.2 ≤ n := by
          calc
            _ = 1 * p.2 := by simp
            _ ≤ p.1 * p.2 := Nat.mul_le_mul_right _ hp1
            _ = _ := (Nat.mem_divisorsAntidiagonal.mp hp).1
        have hp2r : (1 : ℝ) ≤ p.2 := by exact_mod_cast hp2
        have hpow : (Real.log (p.2 : ℝ))^h ≤ (Real.log (n : ℝ))^h :=
          pow_le_pow_left₀ (Real.log_nonneg hp2r)
            (Real.log_le_log (by linarith) (by exact_mod_cast hp2n)) h
        rw [norm_mul]
        exact mul_le_mul (ha p.1) ((ih p.2).trans hpow) (norm_nonneg _)
          ArithmeticFunction.vonMangoldt_nonneg
      _ = (∑ p ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt p.1) *
          (Real.log (n : ℝ))^h := (Finset.sum_mul _ _ _).symm
      _ = (Real.log (n : ℝ))^(h+1) := by
        rw [Nat.sum_divisorsAntidiagonal (fun d _ => ArithmeticFunction.vonMangoldt d),
          ArithmeticFunction.vonMangoldt_sum, pow_succ]
        ring

/-- Actual squared coefficient energy is bounded by its reciprocal mass. -/
theorem weighted_power_energy_le_mass (a : ArithmeticFunction ℂ)
    (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (h D N : ℕ) (hD : 1 ≤ D) (s : Finset ℕ)
    (hs : ∀ n ∈ s, D ≤ n ∧ n ≤ N) :
    (∑ n ∈ s, ‖(a^h) n‖^2 / (n : ℝ)^2) ≤
      ((Real.log (N : ℝ))^h / (D : ℝ)) *
        (∑ n ∈ s, ‖(a^h) n‖ / (n : ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hbounds := hs n hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hD.trans hbounds.1
  have hnp : (0 : ℝ) < n := by linarith
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlogpow : (Real.log (n : ℝ))^h ≤ (Real.log (N : ℝ))^h :=
    pow_le_pow_left₀ (Real.log_nonneg hnr)
      (Real.log_le_log hnp (by exact_mod_cast hbounds.2)) h
  have hb : ‖(a^h) n‖ ≤ (Real.log (N : ℝ))^h :=
    (convolution_power_log_bound a ha h n).trans hlogpow
  have hratio : ‖(a^h) n‖ / (n : ℝ) ≤ (Real.log (N : ℝ))^h / (D : ℝ) := by
    calc
      _ ≤ (Real.log (N : ℝ))^h / (n : ℝ) := div_le_div_of_nonneg_right hb hnp.le
      _ ≤ _ := div_le_div_of_nonneg_left (le_trans (norm_nonneg _) hb) hDp
        (by exact_mod_cast hbounds.1)
  calc
    _ = (‖(a^h) n‖ / (n : ℝ)) * (‖(a^h) n‖ / (n : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio (div_nonneg (norm_nonneg _) hnp.le)

def reciprocalNorm (a : ArithmeticFunction ℂ) : ArithmeticFunction ℝ :=
  ⟨fun n => ‖a n‖ / (n : ℝ), by simp⟩

@[simp] theorem reciprocalNorm_apply (a : ArithmeticFunction ℂ) (n : ℕ) :
    reciprocalNorm a n = ‖a n‖ / (n : ℝ) := rfl

theorem reciprocalNorm_mul_le (a b : ArithmeticFunction ℂ) (n : ℕ) :
    reciprocalNorm (a*b) n ≤ (reciprocalNorm a * reciprocalNorm b) n := by
  rw [reciprocalNorm_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply]
  calc
    _ ≤ (∑ p ∈ n.divisorsAntidiagonal, ‖a p.1 * b p.2‖) / (n : ℝ) :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) (Nat.cast_nonneg n)
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      rw [norm_mul, ← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.cast_mul]
      exact (div_mul_div_comm _ _ _ _).symm

theorem finite_real_convolution_sum (N M : ℕ) (_hN : 1 ≤ N) (hM : 1 ≤ M)
    (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, N < n → f n = 0) (hg : ∀ n, M < n → g n = 0) :
    (∑ n ∈ Finset.Ioc 0 (N*M), (f*g) n) =
      (∑ n ∈ Finset.Ioc 0 N, f n) * (∑ n ∈ Finset.Ioc 0 M, g n) := by
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  have hNM : N ≤ N*M := by nlinarith
  calc
    _ = ∑ d ∈ Finset.Ioc 0 N, f d * ∑ m ∈ Finset.Ioc 0 (N*M/d), g m := by
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
      have hMd : M ≤ N*M/d := (Nat.le_div_iff_mul_le hd0).mpr (by nlinarith)
      symm
      apply Finset.sum_subset (Finset.Ioc_subset_Ioc le_rfl hMd)
      intro m hm hnot
      have hm0 := (Finset.mem_Ioc.mp hm).1
      apply hg
      simpa [Finset.mem_Ioc, hm0] using hnot
    _ = _ := by rw [Finset.sum_mul]

theorem finite_reciprocal_mass_mul_le (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (a b : ArithmeticFunction ℂ)
    (ha : ∀ n, N < n → a n = 0) (hb : ∀ n, M < n → b n = 0) :
    (∑ n ∈ Finset.Ioc 0 (N*M), ‖(a*b) n‖ / (n : ℝ)) ≤
      (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ / (n : ℝ)) *
      (∑ n ∈ Finset.Ioc 0 M, ‖b n‖ / (n : ℝ)) := by
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 (N*M), (reciprocalNorm a * reciprocalNorm b) n :=
      Finset.sum_le_sum (fun n _ => reciprocalNorm_mul_le a b n)
    _ = _ := finite_real_convolution_sum N M hN hM _ _
      (by intro n hn; simp [ha n hn]) (by intro n hn; simp [hb n hn])

theorem power_vanishes_above (a : ArithmeticFunction ℂ) (N : ℕ)
    (ha : ∀ n, N < n → a n = 0) (h n : ℕ) (hn : N^h < n) : (a^h) n = 0 := by
  induction h generalizing n with
  | zero => simp [show n ≠ 1 by simpa using ne_of_gt hn]
  | succ h ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply]
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hp1 : N^h < p.1
    · rw [ih p.1 hp1, zero_mul]
    · have hp2 : N < p.2 := by
        have hpn := (Nat.mem_divisorsAntidiagonal.mp hp).1
        have hp1' : p.1 ≤ N^h := Nat.le_of_not_gt hp1
        by_contra hnot
        have hp2' : p.2 ≤ N := Nat.le_of_not_gt hnot
        have := Nat.mul_le_mul hp1' hp2'
        rw [hpn, ← pow_succ] at this
        exact (not_lt_of_ge this) hn
      rw [ha p.2 hp2, mul_zero]

theorem power_reciprocal_mass_le (a : ArithmeticFunction ℂ) (N : ℕ) (hN : 1 ≤ N)
    (ha : ∀ n, N < n → a n = 0) (h : ℕ) :
    (∑ n ∈ Finset.Ioc 0 (N^h), ‖(a^h) n‖ / (n : ℝ)) ≤
      (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ / (n : ℝ))^h := by
  induction h with
  | zero => simp [show Finset.Ioc 0 1 = {1} by decide, ArithmeticFunction.one_apply]
  | succ h ih =>
    rw [pow_succ a, pow_succ N]
    apply (finite_reciprocal_mass_mul_le (N^h) N (one_le_pow₀ hN) hN (a^h) a
      (fun n hn => power_vanishes_above a N ha h n hn) ha).trans
    simpa only [pow_succ] using mul_le_mul_of_nonneg_right ih
      (Finset.sum_nonneg (fun n _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg n)))

theorem power_support (a : ArithmeticFunction ℂ) (D N : ℕ)
    (hs : ∀ n, a n ≠ 0 → D ≤ n ∧ n ≤ N) (h n : ℕ) (hn : (a^h) n ≠ 0) :
    D^h ≤ n ∧ n ≤ N^h := by
  induction h generalizing n with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply] at hn
    have : n = 1 := by split_ifs at hn with hn1 <;> simp_all
    simp [this]
  | succ h ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply] at hn
    obtain ⟨p, hp, hpne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have hab := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hfirst := ih p.1 (mul_ne_zero_iff.mp hpne).1
    have hsecond := hs p.2 (mul_ne_zero_iff.mp hpne).2
    rw [pow_succ, pow_succ, ← hab]
    exact ⟨Nat.mul_le_mul hfirst.1 hsecond.1, Nat.mul_le_mul hfirst.2 hsecond.2⟩


run_cmd do
  for target in [``convolution_power_log_bound, ``weighted_power_energy_le_mass, ``reciprocalNorm, ``reciprocalNorm_apply, ``reciprocalNorm_mul_le, ``finite_real_convolution_sum, ``finite_reciprocal_mass_mul_le, ``power_vanishes_above, ``power_reciprocal_mass_le, ``power_support] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "MomentResidualConvolution PASSED; 10 declarations guarded"
end MomentResidualConvolution
end
