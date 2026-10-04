import DirichletEvenMoment
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.PSeries

/-! Gaussian smoothing gives a mean-square bound without the harmonic
row loss. All coefficients may be complex and the frequencies are exact. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace GaussianMeanSquareWork
open Erdos374.HarmanAnalytic151MeanSquare

def weight (t : ℝ) : ℝ := Real.exp (-t ^ 2)

theorem integrable_weight_kernel (ξ : ℝ) :
    Integrable (fun t : ℝ => (weight t : ℂ) * exponentialKernel151 ξ t) := by
  have h := integrable_cexp_quadratic (b := (1 : ℂ)) (by norm_num)
    (Complex.I * (ξ : ℂ)) 0
  convert h using 1
  ext t
  simp only [weight, exponentialKernel151, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_pow, ← Complex.exp_add]
  congr 1
  ring

theorem norm_integral_weight_kernel (ξ : ℝ) :
    ‖∫ t : ℝ, (weight t : ℂ) * exponentialKernel151 ξ t‖ =
      Real.sqrt Real.pi * Real.exp (-ξ ^ 2 / 4) := by
  have h := fourierIntegral_gaussian (b := (1 : ℂ)) (by norm_num) (ξ : ℂ)
  have he (t : ℝ) : (weight t : ℂ) * exponentialKernel151 ξ t =
      Complex.exp (Complex.I * (ξ : ℂ) * t) * Complex.exp (-(1 : ℂ) * (t : ℂ)^2) := by
    simp only [weight, exponentialKernel151, Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_pow]
    rw [mul_comm]
    congr 1
    congr 1
    ring
  simp_rw [he]
  rw [h, norm_mul]
  have hc : ‖((Real.pi : ℂ) / 1) ^ (1 / 2 : ℂ)‖ = Real.sqrt Real.pi := by
    rw [div_one]
    convert Complex.norm_cpow_real (Real.pi : ℂ) (1/2 : ℝ) using 1
    · norm_num
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        Real.sqrt_eq_rpow]
  rw [hc, Complex.norm_exp]
  congr 2
  simp [← Complex.ofReal_pow]

theorem integrable_weight_square {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ξ : ι → ℝ) : Integrable (fun t => weight t * ‖exponentialSum151 s a ξ t‖ ^ 2) := by
  have hnorm (t : ℝ) : ‖exponentialSum151 s a ξ t‖ ≤ ∑ i ∈ s, ‖a i‖ := by
    apply (norm_sum_le _ _).trans
    simp only [norm_mul, norm_kernel151, mul_one]
    exact le_rfl
  apply ((integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)).const_mul
    ((∑ i ∈ s, ‖a i‖) ^ 2)).mono'
  · exact ((by unfold weight; fun_prop : Continuous weight).mul
      ((continuous_sum151 s a ξ).norm.pow (2 : ℕ))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold weight; positivity)]
    simpa only [weight, neg_mul, one_mul, mul_comm, mul_neg_one, neg_one_mul] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hnorm t) 2)
        (Real.exp_pos (-t^2)).le

theorem gaussian_square_bound {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ξ : ι → ℝ) (R : ℝ)
    (hrow : ∀ m ∈ s, (∑ n ∈ s, Real.exp (-(ξ m - ξ n)^2/4)) ≤ R) :
    (∫ t : ℝ, weight t * ‖exponentialSum151 s a ξ t‖ ^ 2) ≤
      Real.sqrt Real.pi * R * (∑ n ∈ s, ‖a n‖ ^ 2) := by
  have he : ((∫ t : ℝ, weight t * ‖exponentialSum151 s a ξ t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, a m * conj (a n) *
        (∫ t : ℝ, (weight t : ℂ) * exponentialKernel151 (ξ m - ξ n) t) := by
    rw [← integral_complex_ofReal]
    simp only [Complex.ofReal_mul, norm_square_expansion151,
      Finset.mul_sum]
    have hterm (m n : ι) : Integrable (fun t => (weight t : ℂ) *
        (a m * conj (a n) * exponentialKernel151 (ξ m - ξ n) t)) := by
      convert (integrable_weight_kernel (ξ m - ξ n)).const_mul (a m * conj (a n)) using 1
      ext t
      ring
    rw [integral_finsetSum s (fun m _ => integrable_finsetSum s (fun n _ => hterm m n))]
    apply Finset.sum_congr rfl
    intro m _
    rw [integral_finsetSum s (fun n _ => hterm m n)]
    apply Finset.sum_congr rfl
    intro n _
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by ring)
  have hn := congrArg norm he
  have hnonneg : 0 ≤ ∫ t : ℝ, weight t * ‖exponentialSum151 s a ξ t‖ ^ 2 :=
    integral_nonneg (fun _ => by unfold weight; positivity)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hn
  have hp := quadratic_pair_bound151 s (fun n => ‖a n‖)
    (fun m n => Real.exp (-(ξ m-ξ n)^2/4)) R
    (fun _ _ _ _ => (Real.exp_pos _).le)
    (fun m _ n _ => by congr 1; ring) hrow
  calc
    _ ≤ ∑ m ∈ s, ∑ n ∈ s, ‖a m‖ * ‖a n‖ *
        (Real.sqrt Real.pi * Real.exp (-(ξ m-ξ n)^2/4)) := by
      rw [hn]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro m _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n _
      simp only [norm_mul, RCLike.norm_conj, norm_integral_weight_kernel]
      exact le_rfl
    _ ≤ _ := by
      have heq : (∑ m ∈ s, ∑ n ∈ s, 2 * ‖a m‖ * ‖a n‖ *
          Real.exp (-(ξ m-ξ n)^2/4)) =
          2 * (∑ m ∈ s, ∑ n ∈ s, ‖a m‖ * ‖a n‖ *
            Real.exp (-(ξ m-ξ n)^2/4)) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro n _
        ring
      rw [heq] at hp
      have hh := mul_le_mul_of_nonneg_left (show
          (∑ m ∈ s, ∑ n ∈ s, ‖a m‖ * ‖a n‖ * Real.exp (-(ξ m-ξ n)^2/4)) ≤
            R * (∑ n ∈ s, ‖a n‖ ^ 2) by linarith) (Real.sqrt_nonneg Real.pi)
      apply le_trans (le_of_eq ?_) (hh.trans_eq (by ring))
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      ring

theorem inverse_square_distance_row (s : Finset ℕ) (m N : ℕ)
    (hmN : m ≤ N) (hs : ∀ n ∈ s, n ≤ N) :
    (∑ n ∈ s.erase m, 1 / |(m : ℝ) - n| ^ 2) ≤ 4 := by
  let lo := (s.erase m).filter (· < m)
  let hi := (s.erase m).filter (fun n => ¬n < m)
  have hlo_mem : ∀ n ∈ lo, n < m ∧ n ≤ N := by
    intro n hn
    exact ⟨(Finset.mem_filter.mp hn).2,
      hs n (Finset.mem_erase.mp (Finset.mem_filter.mp hn).1).2⟩
  have hhi_mem : ∀ n ∈ hi, m < n ∧ n ≤ N := by
    intro n hn
    have hh := Finset.mem_filter.mp hn
    have hne := (Finset.mem_erase.mp hh.1).1
    exact ⟨by omega, hs n (Finset.mem_erase.mp hh.1).2⟩
  have hlo_image : lo.image (fun n => m-n) ⊆ Finset.Ioo 0 (N+1) := by
    intro j hj
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
    have := hlo_mem n hn
    simp only [Finset.mem_Ioo]
    omega
  have hhi_image : hi.image (fun n => n-m) ⊆ Finset.Ioo 0 (N+1) := by
    intro j hj
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
    have := hhi_mem n hn
    simp only [Finset.mem_Ioo]
    omega
  have hsum : (∑ j ∈ Finset.Ioo 0 (N+1), ((j : ℝ)^2)⁻¹) ≤ 2 := by
    simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (N+1))
  have hlo : (∑ n ∈ lo, 1 / |(m : ℝ)-n|^2) ≤ 2 := by
    have heq : (∑ n ∈ lo, 1 / |(m : ℝ)-n|^2) =
        ∑ j ∈ lo.image (fun n => m-n), ((j : ℝ)^2)⁻¹ := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro n hn
        have hnm := (hlo_mem n hn).1.le
        rw [Nat.cast_sub hnm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hnm)), one_div]
      · intro n hn j hj heq
        have := hlo_mem n hn
        have := hlo_mem j hj
        dsimp at heq
        omega
    rw [heq]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hlo_image
      (fun j _ _ => by positivity)).trans hsum
  have hhi : (∑ n ∈ hi, 1 / |(m : ℝ)-n|^2) ≤ 2 := by
    have heq : (∑ n ∈ hi, 1 / |(m : ℝ)-n|^2) =
        ∑ j ∈ hi.image (fun n => n-m), ((j : ℝ)^2)⁻¹ := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro n hn
        have hmn := (hhi_mem n hn).1.le
        rw [Nat.cast_sub hmn, abs_sub_comm,
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmn)), one_div]
      · intro n hn j hj heq
        have := hhi_mem n hn
        have := hhi_mem j hj
        dsimp at heq
        omega
    rw [heq]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hhi_image
      (fun j _ _ => by positivity)).trans hsum
  have hsplit := Finset.sum_filter_add_sum_filter_not (s.erase m) (· < m)
    (fun n => 1 / |(m : ℝ)-n|^2)
  change (∑ n ∈ lo, 1 / |(m : ℝ)-n|^2) +
    (∑ n ∈ hi, 1 / |(m : ℝ)-n|^2) = _ at hsplit
  linarith

theorem exp_neg_square_le (ξ : ℝ) (hξ : ξ ≠ 0) :
    Real.exp (-ξ^2/4) ≤ 4/ξ^2 := by
  have hz : 0 < ξ^2/4 := by positivity
  have hh : ξ^2/4 ≤ Real.exp (ξ^2/4) := by linarith [Real.add_one_le_exp (ξ^2/4)]
  rw [show -ξ^2/4 = -(ξ^2/4) by ring, Real.exp_neg]
  have hb := one_div_le_one_div_of_le hz hh
  simpa only [one_div, inv_div, inv_inv] using hb

theorem logarithmic_gaussian_row (s : Finset ℕ) (N : ℕ) (R : ℝ)
    (hN : 1 ≤ N) (hR : (N : ℝ) ≤ R)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (m : ℕ) (hm : m ∈ s) :
    (∑ n ∈ s, Real.exp (-(R*Real.log m-R*Real.log n)^2/4)) ≤ 17 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := hNp.trans_le hR
  have hterm : ∀ n ∈ s.erase m,
      Real.exp (-(R*Real.log m-R*Real.log n)^2/4) ≤ 4/|(m : ℝ)-n|^2 := by
    intro n hn
    have hn' := Finset.mem_erase.mp hn
    have hdist : 0 < |(m : ℝ)-n| := by
      apply abs_pos.mpr
      exact sub_ne_zero.mpr (by exact_mod_cast hn'.1.symm)
    have hlog : 0 < |Real.log m-Real.log n| := by
      apply abs_pos.mpr
      apply sub_ne_zero.mpr
      intro he
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by have := hs m hm; omega)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hs n hn'.2; omega)
      have he' := Real.log_injOn_pos hm0 hn0 he
      exact hn'.1 (Nat.cast_injective he'.symm)
    have hh := inverse_log_difference_le151 (hs m hm).1 (hs n hn'.2).1
      (hs m hm).2 (hs n hn'.2).2 hn'.1.symm
    have hgap : |(m : ℝ)-n| ≤ |R*Real.log m-R*Real.log n| := by
      have hb := (div_le_div_iff₀ hlog hdist).mp hh
      rw [← mul_sub, abs_mul, abs_of_pos hRp]
      nlinarith
    have hξ : R*Real.log m-R*Real.log n ≠ 0 := abs_pos.mp (hdist.trans_le hgap)
    apply (exp_neg_square_le _ hξ).trans
    rw [← sq_abs]
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hdist)
      (pow_le_pow_left₀ (abs_nonneg _) hgap 2)
  have hoff := Finset.sum_le_sum hterm
  have hrow := inverse_square_distance_row s m N (hs m hm).2 (fun n hn => (hs n hn).2)
  have he : (∑ n ∈ s.erase m, 4/|(m : ℝ)-n|^2) =
      4*(∑ n ∈ s.erase m, 1/|(m : ℝ)-n|^2) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he] at hoff
  rw [← Finset.add_sum_erase s _ hm]
  norm_num
  nlinarith

theorem unit_interval_square_bound {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ξ : ι → ℝ) (U R : ℝ) (_hU : 0 ≤ U) (hU1 : U ≤ 1)
    (hrow : ∀ m ∈ s, (∑ n ∈ s, Real.exp (-(ξ m-ξ n)^2/4)) ≤ R) :
    (∫ t in Icc 0 U, ‖exponentialSum151 s a ξ t‖ ^ 2) ≤
      Real.exp 1 * Real.sqrt Real.pi * R * (∑ n ∈ s, ‖a n‖ ^ 2) := by
  have hc := (continuous_sum151 s a ξ).norm.pow (2 : ℕ)
  have hw : Continuous weight := by unfold weight; fun_prop
  have hg := integrable_weight_square s a ξ
  have hpt : ∀ t ∈ Icc 0 U, ‖exponentialSum151 s a ξ t‖ ^ 2 ≤
      Real.exp 1 * (weight t * ‖exponentialSum151 s a ξ t‖ ^ 2) := by
    intro t ht
    have ht1 : t ≤ 1 := ht.2.trans hU1
    have hsq : t^2 ≤ 1 := by nlinarith [ht.1]
    have hh : 1 ≤ Real.exp 1 * weight t := by
      rw [weight, ← Real.exp_add]
      simpa using Real.exp_le_exp.mpr (show 0 ≤ 1 + -t^2 by linarith)
    nlinarith [sq_nonneg ‖exponentialSum151 s a ξ t‖]
  calc
    _ ≤ ∫ t in Icc 0 U, Real.exp 1 * (weight t * ‖exponentialSum151 s a ξ t‖^2) :=
      setIntegral_mono_on (hc.integrableOn_Icc) ((hw.mul hc).const_mul _).integrableOn_Icc
        measurableSet_Icc hpt
    _ = Real.exp 1 * (∫ t in Icc 0 U, weight t * ‖exponentialSum151 s a ξ t‖^2) :=
      integral_const_mul _ _
    _ ≤ Real.exp 1 * (∫ t : ℝ, weight t * ‖exponentialSum151 s a ξ t‖^2) :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hg
        (Filter.Eventually.of_forall (fun _ => by unfold weight; positivity))) (Real.exp_pos 1).le
    _ ≤ _ := (mul_le_mul_of_nonneg_left (gaussian_square_bound s a ξ R hrow)
      (Real.exp_pos 1).le).trans_eq (by ring)

theorem exponential_affine (s : Finset ℕ) (coeff : ℕ → ℂ) (a R u : ℝ) :
    exponentialSum151 s coeff (fun n => Real.log n) (a+R*u) =
      exponentialSum151 s (fun n => coeff n * exponentialKernel151 (Real.log n) a)
        (fun n => R * Real.log n) u := by
  unfold exponentialSum151
  apply Finset.sum_congr rfl
  intro n _
  unfold exponentialKernel151
  dsimp only
  conv_rhs => rw [mul_assoc]
  rw [← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

def meanSquareConstant : ℝ := 17 * Real.exp 1 * Real.sqrt Real.pi

theorem meanSquareConstant_pos : 0 < meanSquareConstant := by
  unfold meanSquareConstant
  positivity

theorem dirichlet_mean_square_max (s : Finset ℕ) (coeff : ℕ → ℂ) (N : ℕ)
    (a T : ℝ) (hN : 1 ≤ N) (hT : 0 ≤ T)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) :
    (∫ t in Icc a (a+T), ‖exponentialSum151 s coeff (fun n => Real.log n) t‖^2) ≤
      meanSquareConstant * max T (N : ℝ) * (∑ n ∈ s, ‖coeff n‖^2) := by
  let R : ℝ := max T (N : ℝ)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := hNp.trans_le (le_max_right _ _)
  have hU : 0 ≤ T/R := div_nonneg hT hRp.le
  have hU1 : T/R ≤ 1 := (div_le_one hRp).mpr (le_max_left _ _)
  let b : ℕ → ℂ := fun n => coeff n * exponentialKernel151 (Real.log n) a
  have hb : ∑ n ∈ s, ‖b n‖^2 = ∑ n ∈ s, ‖coeff n‖^2 := by
    simp only [b, norm_mul, norm_kernel151, mul_one]
  have hrow := logarithmic_gaussian_row s N R hN (le_max_right _ _) hs
  have hm := unit_interval_square_bound s b (fun n => R * Real.log n) (T/R) 17 hU hU1 hrow
  rw [hb] at hm
  have hchange : (∫ t in Icc a (a+T),
      ‖exponentialSum151 s coeff (fun n => Real.log n) t‖^2) =
      R * (∫ u in Icc 0 (T/R),
        ‖exponentialSum151 s b (fun n => R * Real.log n) u‖^2) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show a ≤ a+T by linarith)]
    have hh := intervalIntegral.smul_integral_comp_add_mul
      (fun t => ‖exponentialSum151 s coeff (fun n => Real.log n) t‖^2)
      (a := 0) (b := T/R) R a
    simp only [smul_eq_mul, mul_zero, add_zero, mul_div_cancel₀ _ hRp.ne'] at hh
    rw [← hh]
    simp_rw [exponential_affine]
    rw [intervalIntegral.integral_of_le hU, ← integral_Icc_eq_integral_Ioc]
  rw [hchange]
  exact (mul_le_mul_of_nonneg_left hm hRp.le).trans_eq (by
    dsimp [R, meanSquareConstant]
    ring)

theorem dirichlet_mean_square_bound (s : Finset ℕ) (coeff : ℕ → ℂ) (N : ℕ)
    (a T : ℝ) (hN : 1 ≤ N) (hT : 0 ≤ T)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) :
    (∫ t in Icc a (a+T), ‖exponentialSum151 s coeff (fun n => Real.log n) t‖^2) ≤
      meanSquareConstant * (T + N) * (∑ n ∈ s, ‖coeff n‖^2) := by
  apply (dirichlet_mean_square_max s coeff N a T hN hT hs).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  apply mul_le_mul_of_nonneg_left _ meanSquareConstant_pos.le
  exact max_le (le_add_of_nonneg_right (Nat.cast_nonneg N)) (le_add_of_nonneg_left hT)

#print axioms dirichlet_mean_square_bound
#print axioms gaussian_square_bound
#print axioms logarithmic_gaussian_row
run_cmd do
  for decl in [``integrable_weight_kernel, ``norm_integral_weight_kernel,
      ``integrable_weight_square, ``gaussian_square_bound,
      ``inverse_square_distance_row, ``exp_neg_square_le, ``logarithmic_gaussian_row,
      ``unit_interval_square_bound, ``exponential_affine, ``meanSquareConstant_pos,
      ``dirichlet_mean_square_max, ``dirichlet_mean_square_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "GAUSSIAN MEAN SQUARE PASSED"
end GaussianMeanSquareWork
