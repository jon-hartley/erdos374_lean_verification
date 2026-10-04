import PairFourierCoefficients

/-! Finite hard Fourier projection. Every mode sharing a physical frequency
is retained by the same physical cutoff. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set intervalIntegral
open scoped Real ENNReal BigOperators

namespace PairFourier

def projection (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (S : Finset ℤ) (x : ℝ) : ℂ :=
  ∑ k ∈ S, fourierCoeffOn hT f k * phase T k x

def hardModes (n F : ℕ) : Finset ℤ := Finset.Icc (-(n*F:ℕ):ℤ) (n*F:ℕ)

def hardProjection (n : ℕ) (hn : 0 < n) (h : ℝ) (F : ℕ) : ℝ → ℂ :=
  projection n (by exact_mod_cast hn) (discrepancy n h) (hardModes n F)

theorem projection_continuous (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (S : Finset ℤ) :
    Continuous (projection T hT f S) := by
  unfold projection
  exact continuous_finsetSum S (fun k _ => continuous_const.mul (phase_continuous T k))

theorem projection_periodic (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (S : Finset ℤ) :
    Function.Periodic (projection T hT f S) T := by
  intro x
  unfold projection
  apply Finset.sum_congr rfl
  intro k _
  rw [phase_periodic T k]

theorem phase_mul (T : ℝ) (j k : ℤ) (x : ℝ) :
    phase T j x * phase T k x = phase T (j+k) x := by
  exact (fourier_add (x := (x : AddCircle T))).symm

theorem coefficient_phase (T : ℝ) (hT : 0 < T) (j k : ℤ) :
    fourierCoeffOn hT (phase T j) k = if k = j then 1 else 0 := by
  rw [coefficient_eq_integral]
  have hi : (∫ x in (0:ℝ)..T, phase T (-k) x * phase T j x) =
      ∫ x in (0:ℝ)..T, phase T (-k+j) x := by
    congr 1
    funext x
    exact phase_mul T (-k) j x
  rw [hi]
  split_ifs with hkj
  · subst k
    simp only [neg_add_cancel, phase_zero, intervalIntegral.integral_const, sub_zero,
      Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
    norm_cast
    field_simp
  · have hkj0 : -k+j ≠ 0 := by omega
    rw [integral_phase T hT.ne' _ hkj0, phase_at_period, phase_at_zero,
      sub_self, mul_zero, smul_zero]

theorem coefficient_sum {ι : Type*} (T : ℝ) (hT : 0 < T) (S : Finset ι)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ S, IntervalIntegrable (f i) volume 0 T) (k : ℤ) :
    fourierCoeffOn hT (fun x => ∑ i ∈ S, f i x) k =
      ∑ i ∈ S, fourierCoeffOn hT (f i) k := by
  simp only [coefficient_eq_integral, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.smul_sum
  · intro i hi
    simpa only [mul_comm] using
      (hf i hi).mul_continuousOn (phase_continuous T (-k)).continuousOn

theorem coefficient_sub (T : ℝ) (hT : 0 < T) (f g : ℝ → ℂ)
    (hf : IntervalIntegrable f volume 0 T) (hg : IntervalIntegrable g volume 0 T) (k : ℤ) :
    fourierCoeffOn hT (fun x => f x - g x) k =
      fourierCoeffOn hT f k - fourierCoeffOn hT g k := by
  simp only [coefficient_eq_integral, mul_sub]
  rw [intervalIntegral.integral_sub, smul_sub]
  · simpa only [mul_comm] using hf.mul_continuousOn (phase_continuous T (-k)).continuousOn
  · simpa only [mul_comm] using hg.mul_continuousOn (phase_continuous T (-k)).continuousOn

theorem coefficient_projection (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ)
    (S : Finset ℤ) (k : ℤ) :
    fourierCoeffOn hT (projection T hT f S) k =
      if k ∈ S then fourierCoeffOn hT f k else 0 := by
  classical
  unfold projection
  rw [coefficient_sum T hT S]
  · simp only [fourierCoeffOn.const_mul, coefficient_phase]
    simp [mul_ite]
  · intro j _
    exact (continuous_const.mul (phase_continuous T j)).intervalIntegrable 0 T

theorem projection_norm_le (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ)
    (S : Finset ℤ) (x : ℝ) :
    ‖projection T hT f S x‖ ≤ ∑ k ∈ S, ‖fourierCoeffOn hT f k‖ := by
  unfold projection
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul, phase_norm, mul_one])

theorem projection_memLp (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (S : Finset ℤ)
    (a b : ℝ) (p : ℝ≥0∞) :
    MemLp (projection T hT f S) p (volume.restrict (Ioc a b)) := by
  apply MemLp.of_bound (projection_continuous T hT f S).aestronglyMeasurable
    (∑ k ∈ S, ‖fourierCoeffOn hT f k‖)
  exact Filter.Eventually.of_forall (projection_norm_le T hT f S)

theorem coefficient_residual (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume 0 T) (S : Finset ℤ) (k : ℤ) :
    fourierCoeffOn hT (fun x => f x - projection T hT f S x) k =
      if k ∈ S then 0 else fourierCoeffOn hT f k := by
  rw [coefficient_sub T hT f _ hf ((projection_continuous T hT f S).intervalIntegrable 0 T),
    coefficient_projection]
  split_ifs <;> simp

theorem discrepancy_residual_memLp (n : ℕ) (hn : 0 < n) (h : ℝ) (F : ℕ)
    (a b : ℝ) (p : ℝ≥0∞) :
    MemLp (fun x => discrepancy n h x - hardProjection n hn h F x)
      p (volume.restrict (Ioc a b)) := by
  exact (discrepancy_memLp n h a b p).sub (projection_memLp _ _ _ _ a b p)

end PairFourier
