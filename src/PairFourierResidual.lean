import PairFourierProjection
import PairCommonPeriod
import PairReciprocalTail

/-! Parseval for the residual of a finite hard Fourier projection. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set intervalIntegral
open scoped Real ENNReal BigOperators

namespace PairFourier

/-- Exact normalized residual energy; finite projection coefficients are
proved in `coefficient_residual`, so the retained modes vanish exactly. -/
theorem residual_parseval (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 T))) (S : Finset ℤ) :
    (1/T) * (∫ x in (0:ℝ)..T, ‖f x - projection T hT f S x‖^2) =
      ∑' k : ℤ, if k ∈ S then 0 else ‖fourierCoeffOn hT f k‖^2 := by
  have hres : MemLp (fun x => f x - projection T hT f S x) 2
      (volume.restrict (Ioc 0 T)) := hf.sub (projection_memLp T hT f S 0 T 2)
  have hi : IntervalIntegrable f volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr (hf.integrable (by norm_num))
  have hp := tsum_sq_fourierCoeffOn hT hres
  simp only [sub_zero, smul_eq_mul, ← one_div] at hp
  rw [← hp]
  apply tsum_congr
  intro k
  rw [coefficient_residual T hT f hi S k]
  split_ifs <;> simp

theorem residual_coefficients_summable (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 T))) (S : Finset ℤ) :
    Summable (fun k : ℤ => if k ∈ S then 0 else ‖fourierCoeffOn hT f k‖^2) := by
  have hres : MemLp (fun x => f x - projection T hT f S x) 2
      (volume.restrict (Ioc 0 T)) := hf.sub (projection_memLp T hT f S 0 T 2)
  have hi : IntervalIntegrable f volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr (hf.integrable (by norm_num))
  have hs := (hasSum_sq_fourierCoeffOn hT hres).summable
  convert hs using 1
  funext k
  rw [coefficient_residual T hT f hi S k]
  split_ifs <;> simp

theorem hard_residual_periodic (n : ℕ) (hn : 0 < n) (h : ℝ) (F : ℕ) :
    Function.Periodic (fun x => ‖discrepancy n h x - hardProjection n hn h F x‖^2)
      (n:ℝ) := by
  intro x
  dsimp only
  rw [discrepancy_periodic n hn h, hardProjection, projection_periodic]

theorem hard_residual_integrable (n : ℕ) (hn : 0 < n) (h : ℝ) (F : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => ‖discrepancy n h x - hardProjection n hn h F x‖^2)
      volume a b := by
  constructor <;>
    exact (discrepancy_residual_memLp n hn h F _ _ 2).integrable_norm_pow (by norm_num)

theorem mem_hardModes (n F : ℕ) (k : ℤ) :
    k ∈ hardModes n F ↔ |k| ≤ (n*F:ℕ) := by
  simp only [hardModes, Finset.mem_Icc, abs_le]

/-- The quantitative tail bound is uniform in the real width `h`. -/
theorem hard_residual_period_bound (n : ℕ) (hn : 0 < n) (h : ℝ) (F : ℕ) (hF : 0 < F) :
    (∫ x in (0:ℝ)..n, ‖discrepancy n h x - hardProjection n hn h F x‖^2) ≤
      4/(F:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hF0 : (F:ℝ) ≠ 0 := by exact_mod_cast hF.ne'
  have hK : 1 ≤ n*F := Nat.succ_le_iff.mpr (Nat.mul_pos hn hF)
  have hs := residual_coefficients_summable (n:ℝ) hnR (discrepancy n h)
    (discrepancy_memLp n h 0 n 2) (hardModes n F)
  have ht := PairReciprocalTail.summable_tail (n*F) hK
  have hcomp : (∑' k:ℤ, if k ∈ hardModes n F then 0 else
      ‖fourierCoeffOn hnR (discrepancy n h) k‖^2) ≤
      ∑' k:ℤ, PairReciprocalTail.fourierTail (n*F) k := by
    apply Summable.tsum_le_tsum _ hs ht
    intro k
    by_cases hk : k ∈ hardModes n F
    · rw [ite_eq_left hk]
      unfold PairReciprocalTail.fourierTail
      split_ifs <;> positivity
    · have hkm : ((n*F:ℕ):ℤ) < |k| := lt_of_not_ge ((mem_hardModes n F k).not.mp hk)
      have hk0 : k ≠ 0 := by
        intro he
        subst k
        have := Int.natCast_nonneg (n*F)
        simp only [abs_zero] at hkm
        omega
      simp only [ite_eq_right hk, PairReciprocalTail.fourierTail, ite_eq_left hkm]
      exact pow_le_pow_left₀ (norm_nonneg _) (coefficient_norm_le hn h hk0) 2
  have hb := hcomp.trans (PairReciprocalTail.tsum_tail_le_four (n*F) hK)
  rw [← residual_parseval (n:ℝ) hnR (discrepancy n h)
    (discrepancy_memLp n h 0 n 2) (hardModes n F)] at hb
  change (1/(n:ℝ)) * (∫ x in (0:ℝ)..n,
    ‖discrepancy n h x - hardProjection n hn h F x‖^2) ≤ 4/(n*F:ℕ) at hb
  rw [one_div, ← div_eq_inv_mul] at hb
  calc
    _ ≤ (4/(n*F:ℕ)) * (n:ℝ) := (div_le_iff₀ hnR).mp hb
    _ = _ := by push_cast; field_simp

/-- Arbitrary real starting points and every nonnegative interval length. -/
theorem hard_residual_interval_bound (n : ℕ) (hn : 0 < n) (h : ℝ) (F : ℕ) (hF : 0 < F)
    (t T : ℝ) (hT : 0 ≤ T) :
    (∫ x in t..t+T, ‖discrepancy n h x - hardProjection n hn h F x‖^2) ≤
      (4/(F:ℝ)) * (T/n+1) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  calc
    _ ≤ (T/n+1) * (∫ x in (0:ℝ)..n,
        ‖discrepancy n h x - hardProjection n hn h F x‖^2) :=
      PairCommonPeriod.integral_le_cover _ n hnR (hard_residual_periodic n hn h F)
        (hard_residual_integrable n hn h F) (fun _ => sq_nonneg _) t T hT
    _ ≤ (T/n+1) * (4/(F:ℝ)) :=
      mul_le_mul_of_nonneg_left (hard_residual_period_bound n hn h F hF) (by positivity)
    _ = _ := mul_comm _ _

end PairFourier
