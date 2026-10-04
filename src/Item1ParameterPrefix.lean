import Item1ParameterChoice
import Item1ParameterErrors

/-! Transfer an explicit bound for the polynomial averages to the original
logarithmic prefix. The inner estimate is retained as an explicit hypothesis;
the Taylor and endpoint errors are proved from the concrete scale. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace Item1ParameterPrefix
open Item1ParameterCore Item1ParameterChoice Item1ParameterErrors
open Item1FiniteAbelPhase Item1LongLogPhase Item1ProductPrefixMoment
open Item1PrefixNumericalReduction

theorem degree_lower (lam : ℝ) : 3*lam+2 ≤ (degree lam:ℝ) := by
  have hc := Nat.le_ceil (3*lam)
  simp only [degree, Nat.cast_add, Nat.cast_ofNat]
  linarith

theorem scale_square_le_exp {M : ℕ} (hM : 8 ≤ M) :
    (scale M:ℝ)^2 ≤ Real.exp (2*Real.log (M:ℝ)/3) := by
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hscale := (scale_bounds hM).2.2.1
  calc
    (scale M:ℝ)^2 ≤ ((M:ℝ)^(1/3:ℝ))^2 := pow_le_pow_left₀ (by positivity) hscale 2
    _ = Real.exp (2*Real.log (M:ℝ)/3) := by
      rw [Real.rpow_def_of_pos hM0, ← Real.exp_nat_mul]
      congr 1
      ring

theorem scale_ratio_le_exp {M : ℕ} (hM : 8 ≤ M) :
    (scale M:ℝ)^2/(M:ℝ) ≤ Real.exp (-Real.log (M:ℝ)/3) := by
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast (show 0 < M by omega)
  calc
    (scale M:ℝ)^2/(M:ℝ) ≤ Real.exp (2*Real.log (M:ℝ)/3)/(M:ℝ) :=
      div_le_div_of_nonneg_right (scale_square_le_exp hM) hM0.le
    _ = Real.exp (2*Real.log (M:ℝ)/3)/Real.exp (Real.log (M:ℝ)) := by
      rw [Real.exp_log hM0]
    _ = Real.exp (-Real.log (M:ℝ)/3) := by
      rw [← Real.exp_sub]
      congr 1
      ring

theorem chosen_taylor_error_le_two (M K : ℕ) (lam : ℝ)
    (hM : 8 ≤ M) (hK : K ≤ M) :
    (K:ℝ)*(2*|(M:ℝ)^lam| *((scale M:ℝ)^2/(M:ℝ))^(degree lam+1)) ≤ 2 := by
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
  apply taylor_error_le_two (K:ℝ) ((M:ℝ)^lam) ((scale M:ℝ)^2/(M:ℝ))
    (Real.log (M:ℝ)) lam (degree lam) (by positivity)
  · rw [Real.exp_log hM0]
    exact_mod_cast hK
  · rw [Real.rpow_def_of_pos hM0]
    congr 1
    ring
  · positivity
  · exact scale_ratio_le_exp hM
  · exact Real.log_nonneg hM1
  · exact degree_lower lam

theorem prefix_le_of_inner_bound (M K : ℕ) (lam : ℝ)
    (hM : 8 ≤ M) (hlam : 1 ≤ lam) (hK : K ≤ M)
    (hinner : ∀ n : ℕ, n < K →
      ‖U (positiveSet (scale M)) (degree lam) (scale M)
        ((M:ℝ)+n) ((M:ℝ)^lam)‖/(scale M:ℝ)^2 ≤
          Real.exp (-Real.log (M:ℝ)/(4000000*lam^2))) :
    ‖«prefix» (atom M ((M:ℝ)^lam)) K‖ ≤
      5*(M:ℝ)*Real.exp (-Real.log (M:ℝ)/(4000000*lam^2)) := by
  let A := scale M
  let B := positiveSet A
  let d := degree lam
  let t := (M:ℝ)^lam
  let m := Real.log (M:ℝ)
  let δ := Real.exp (-m/(4000000*lam^2))
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
  have hm : 0 ≤ m := Real.log_nonneg hM1
  obtain ⟨hA, _, _, hhalf⟩ := scale_bounds hM
  have hBne : B.Nonempty := positiveSet_nonempty hA
  have hBmax : ∀ b ∈ B, b ≤ A := fun b hb => ((positiveSet_mem A b).mp hb).2
  have hcard : B.card=A := positiveSet_card A
  have hp := (prefix_and_numerical_even_moments B hBne d M K A A 1 1 t
    (by omega) hA hBmax hhalf (by norm_num) (by norm_num)).1
  rw [hcard] at hp
  have havg : (1/((A:ℝ)*(A:ℝ)))*
      (∑ n ∈ Finset.range K, ‖U B d A ((M:ℝ)+n) t‖) ≤ (M:ℝ)*δ := by
    calc
      (1/((A:ℝ)*(A:ℝ)))*(∑ n ∈ Finset.range K, ‖U B d A ((M:ℝ)+n) t‖) =
          ∑ n ∈ Finset.range K, ‖U B d A ((M:ℝ)+n) t‖/(A:ℝ)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        simp only [pow_two, div_eq_mul_inv]
        ring
      _ ≤ ∑ _n ∈ Finset.range K, δ := by
        apply Finset.sum_le_sum
        intro n hn
        exact hinner n (Finset.mem_range.mp hn)
      _ = (K:ℝ)*δ := by simp [nsmul_eq_mul]
      _ ≤ (M:ℝ)*δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hK) (Real.exp_nonneg _)
  have htaylor : (K:ℝ)*(2*|t| *((((A*A:ℕ):ℝ))/(M:ℝ))^(d+1)) ≤ 2 := by
    simpa only [Nat.cast_mul, pow_two] using chosen_taylor_error_le_two M K lam hM hK
  have hboundary : 2*(A:ℝ)*(A:ℝ) ≤ 2*Real.exp (2*m/3) := by
    calc
      2*(A:ℝ)*(A:ℝ) = 2*(A:ℝ)^2 := by ring
      _ ≤ 2*Real.exp (2*m/3) := mul_le_mul_of_nonneg_left (scale_square_le_exp hM) (by norm_num)
  have hall : ‖«prefix» (atom M t) K‖ ≤ (M:ℝ)*δ+2+2*Real.exp (2*m/3) :=
    hp.trans (add_le_add (add_le_add havg htaylor) hboundary)
  have hresult := prefix_errors_absorbed (‖«prefix» (atom M t) K‖) m lam hm hlam
    (by simpa only [m, δ, Real.exp_log hM0] using hall)
  simpa only [m, t, Real.exp_log hM0] using hresult

theorem rpow_log_div (M t : ℝ) (hM : 1 < M) (ht : 0 < t) :
    M^(Real.log t/Real.log M)=t := by
  have hM0 : 0 < M := by linarith
  have hlog : Real.log M ≠ 0 := ne_of_gt (Real.log_pos hM)
  calc
    M^(Real.log t/Real.log M) = Real.exp (Real.log t) := by
      rw [Real.rpow_def_of_pos hM0]
      congr 1
      field_simp
    _ = t := Real.exp_log ht

end Item1ParameterPrefix

run_cmd do
  for target in [``Item1ParameterPrefix.degree_lower,
      ``Item1ParameterPrefix.scale_square_le_exp,
      ``Item1ParameterPrefix.scale_ratio_le_exp,
      ``Item1ParameterPrefix.chosen_taylor_error_le_two,
      ``Item1ParameterPrefix.prefix_le_of_inner_bound,
      ``Item1ParameterPrefix.rpow_log_div] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER PREFIX: 6 standard-axiom theorem guards passed."
