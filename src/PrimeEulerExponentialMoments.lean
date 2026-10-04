import PrimeEulerExponentialBound

/-! The first two logarithmically weighted moments of the actual finite prime
Euler measure. Positivity and monotonicity of each test are proved, and both
endpoint and density comparison errors are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators

namespace PrimeEulerExponentialMoments
open PrimeEulerExponentialCalculus PrimeEulerWeightedTransfer PrimeEulerLogBounds
open SieveStoppingExpansion

def poly : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, v => v+1
  | 2, v => v^2+2*v+2
  | _, v => v^3+3*v^2+6*v+6

def psi (A : ℝ) (n : ℕ) (x : ℝ) : ℝ := test A x*(A/log x)^n
def psiD (A : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  A*logKernel A 2 x*((A/log x)^n-(n:ℝ)*(A/log x)^(n-1))
def primitive (A : ℝ) (n : ℕ) (x : ℝ) : ℝ := test A x*poly n (A/log x)/A

theorem poly_hasDerivAt (n : ℕ) (v : ℝ) (hn : n ≤ 3) :
    HasDerivAt (poly n) (poly n v-v^n) v := by
  interval_cases n
  · convert! hasDerivAt_const v (1:ℝ) using 1; simp [poly]
  · convert! (hasDerivAt_id v).add_const 1 using 1; simp [poly]
  · convert! (((hasDerivAt_id v).pow 2).add ((hasDerivAt_id v).const_mul 2)).add_const 2
      using 1; simp [poly]; ring_nf
  · convert! (((((hasDerivAt_id v).pow 3).add
      (((hasDerivAt_id v).pow 2).const_mul 3)).add
      ((hasDerivAt_id v).const_mul 6)).add_const 6) using 1; simp [poly]; ring_nf

theorem poly_nonneg (n : ℕ) (v : ℝ) (hn : n ≤ 3) (hv : 0 ≤ v) : 0 ≤ poly n v := by
  interval_cases n <;> simp only [poly] <;> positivity

theorem psi_hasDerivAt (A x : ℝ) (n : ℕ) (hx : 1 < x) :
    HasDerivAt (psi A n) (psiD A n x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hl0 : log x ≠ 0 := ne_of_gt (log_pos hx)
  have hv := (hasDerivAt_const x A).div (hasDerivAt_log hx0) hl0
  convert! (PrimeEulerExponentialCalculus.test_hasDerivAt A x hx).mul (hv.pow n) using 1
  dsimp [psiD, logKernel]
  field_simp
  ring

theorem psi_nonneg (A x : ℝ) (n : ℕ) (hA : 0 ≤ A) (hx : 1 < x) :
    0 ≤ psi A n x :=
  mul_nonneg (test_pos A x).le (pow_nonneg (div_nonneg hA (log_pos hx).le) _)

theorem psiD_nonneg (A x : ℝ) (n : ℕ) (hn : n ≤ 2)
    (hA : 0 ≤ A) (hx : 1 < x) (hv : 2 ≤ A/log x) : 0 ≤ psiD A n x := by
  have hp : 0 ≤ A*logKernel A 2 x := mul_nonneg hA (logKernel_nonneg A x 2 hx)
  unfold psiD
  apply mul_nonneg hp
  interval_cases n <;> norm_num <;> nlinarith

theorem psi_continuousOn (A a b : ℝ) (n : ℕ) (ha : 1 < a) :
    ContinuousOn (psi A n) (Icc a b) := by
  intro x hx
  exact (psi_hasDerivAt A x n (ha.trans_le hx.1)).continuousAt.continuousWithinAt

theorem psiD_continuousOn (A a b : ℝ) (n : ℕ) (ha : 1 < a) :
    ContinuousOn (psiD A n) (Icc a b) := by
  have hx0 : ∀ x ∈ Icc a b, x ≠ 0 := fun x hx => by linarith [hx.1]
  have hl0 : ∀ x ∈ Icc a b, log x ≠ 0 :=
    fun x hx => ne_of_gt (log_pos (ha.trans_le hx.1))
  have hv : ContinuousOn (fun x => A/log x) (Icc a b) :=
    continuousOn_const.div (continuousOn_id.log hx0) hl0
  exact ((logKernel_continuousOn A a b 2 ha).const_mul A).mul
    ((hv.pow n).sub ((hv.pow (n-1)).const_mul n))

theorem primitive_hasDerivAt (A x : ℝ) (n : ℕ) (hn : n ≤ 3)
    (hA : 0 < A) (hx : 1 < x) :
    HasDerivAt (primitive A n) (psi A n x/(x*(log x)^2)) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hl0 : log x ≠ 0 := ne_of_gt (log_pos hx)
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hv := (hasDerivAt_const x A).div (hasDerivAt_log hx0) hl0
  convert! ((PrimeEulerExponentialCalculus.test_hasDerivAt A x hx).mul
    ((poly_hasDerivAt n (A/log x) hn).comp x hv)).div_const A using 1
  dsimp [psi]
  field_simp
  ring

theorem primitive_cube_hasDerivAt (A x : ℝ) (n : ℕ) (hn : n ≤ 2)
    (hA : 0 < A) (hx : 1 < x) :
    HasDerivAt (fun y => primitive A (n+1) y/A) (psi A n x/(x*(log x)^3)) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hl0 : log x ≠ 0 := ne_of_gt (log_pos hx)
  have hA0 : A ≠ 0 := ne_of_gt hA
  convert! (primitive_hasDerivAt A x (n+1) (by omega) hA hx).div_const A using 1
  dsimp [psi]
  simp only [pow_succ]
  field_simp [hA0, hx0, hl0]

theorem primitive_nonneg (A x : ℝ) (n : ℕ) (hn : n ≤ 3)
    (hA : 0 < A) (hx : 1 < x) : 0 ≤ primitive A n x :=
  div_nonneg (mul_nonneg (test_pos A x).le
    (poly_nonneg n _ hn (div_pos hA (log_pos hx)).le)) hA.le

theorem kernel_intervalIntegrable (A a b : ℝ) (n k : ℕ)
    (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => psi A n x/(x*(log x)^k)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  have hx0 : ∀ x ∈ Icc a b, x ≠ 0 := fun x hx => by linarith [hx.1]
  have hl0 : ∀ x ∈ Icc a b, log x ≠ 0 :=
    fun x hx => ne_of_gt (log_pos (by linarith [hx.1]))
  exact (psi_continuousOn A a b n (by linarith)).div
    (continuousOn_id.mul ((continuousOn_id.log hx0).pow k))
    (fun x hx => mul_ne_zero (hx0 x hx) (pow_ne_zero _ (hl0 x hx)))

theorem integral_kernel_two_le (A a b : ℝ) (n : ℕ) (hn : n ≤ 3)
    (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, psi A n x/(x*(log x)^2)) ≤ primitive A n b := by
  have heq : (∫ x in a..b, psi A n x/(x*(log x)^2)) =
      primitive A n b - primitive A n a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [uIcc_of_le hab] at hx
      exact primitive_hasDerivAt A x n hn hA (by linarith [hx.1])
    · exact kernel_intervalIntegrable A a b n 2 ha hab
  rw [heq]
  exact sub_le_self _ (primitive_nonneg A a n hn hA (by linarith))

theorem integral_kernel_three_le (A a b : ℝ) (n : ℕ) (hn : n ≤ 2)
    (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, psi A n x/(x*(log x)^3)) ≤ primitive A (n+1) b/A := by
  have heq : (∫ x in a..b, psi A n x/(x*(log x)^3)) =
      primitive A (n+1) b/A - primitive A (n+1) a/A := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [uIcc_of_le hab] at hx
      exact primitive_cube_hasDerivAt A x n hn hA (by linarith [hx.1])
    · exact kernel_intervalIntegrable A a b n 3 ha hab
  rw [heq]
  exact sub_le_self _ (div_nonneg (primitive_nonneg A a (n+1) (by omega) hA (by linarith)) hA.le)

theorem interval_psi_bound (A a b : ℝ) (n : ℕ) (hn : n ≤ 2)
    (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) (hr : 2 ≤ A/log b) :
    (∑ p ∈ intervalPrimes a b, psi A n p*(PrimeEulerMass.weight p/primeEuler b)) ≤
      psi A n b*(PrimeEulerDimensionOne.errorConstant/log b) +
        log b*primitive A n b +
          (2*PrimeEulerDimensionOne.errorConstant*log b)*(primitive A (n+1) b/A) := by
  have hlb : 0 < log b := log_pos (by linarith)
  have hvar : ∀ x ∈ Icc a b, 2 ≤ A/log x := by
    intro x hx
    exact hr.trans (div_le_div_of_nonneg_left hA.le (log_pos (by linarith [hx.1]))
      (log_le_log (by linarith [hx.1]) hx.2))
  have hh := prime_weighted_transfer_density (psi A n) (psiD A n) a b ha hab
    (psi_nonneg A a n hA.le (by linarith)) (psi_continuousOn A a b n (by linarith))
    (psiD_continuousOn A a b n (by linarith))
    (fun x hx => psiD_nonneg A x n hn hA.le (by linarith [hx.1]) (hvar x hx))
    (fun x hx => psi_hasDerivAt A x n (by linarith [hx.1]))
  have hi2 := kernel_intervalIntegrable A a b n 2 ha hab
  have hi3 := kernel_intervalIntegrable A a b n 3 ha hab
  have heq : (fun t => psi A n t*tailDensity t b) =
      (fun t => log b*(psi A n t/(t*(log t)^2)) +
        (2*PrimeEulerDimensionOne.errorConstant*log b)*(psi A n t/(t*(log t)^3))) := by
    funext t
    unfold tailDensity
    ring
  rw [heq, intervalIntegral.integral_add (hi2.const_mul _) (hi3.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hh
  have hc : 0 ≤ 2*PrimeEulerDimensionOne.errorConstant*log b :=
    mul_nonneg (mul_nonneg (by norm_num) PrimeEulerDimensionOne.errorConstant_pos.le) hlb.le
  have h2 := mul_le_mul_of_nonneg_left (integral_kernel_two_le A a b n (by omega) hA ha hab) hlb.le
  have h3 := mul_le_mul_of_nonneg_left (integral_kernel_three_le A a b n hn hA ha hab) hc
  linarith

theorem interval_moment_le (A a b : ℝ) (n : ℕ) (hn : n ≤ 2)
    (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) (hr : 2 ≤ A/log b) :
    (∑ p ∈ intervalPrimes a b, (log b/log p)^n*test A p*
      (PrimeEulerMass.weight p/primeEuler b)) ≤
      exp (1-A/log b)*(poly n (A/log b)/(A/log b)^(n+1) +
        (PrimeEulerDimensionOne.errorConstant/log b)*
          (1+2*poly (n+1) (A/log b)/(A/log b)^(n+2))) := by
  have hAn : A ≠ 0 := ne_of_gt hA
  have hBn : log b ≠ 0 := ne_of_gt (log_pos (by linarith : 1 < b))
  have hrp : 0 < (A/log b)^n := pow_pos (by linarith) _
  have heq : (∑ p ∈ intervalPrimes a b, (log b/log p)^n*test A p*
      (PrimeEulerMass.weight p/primeEuler b)) =
      (∑ p ∈ intervalPrimes a b, psi A n p*(PrimeEulerMass.weight p/primeEuler b))/(A/log b)^n := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    have hp1 : (1:ℝ) < p := by exact_mod_cast ((mem_intervalPrimes a b p).mp hp).1.one_lt
    have hpn : log (p:ℝ) ≠ 0 := ne_of_gt (log_pos hp1)
    unfold psi
    rw [show A/log (p:ℝ) = (A/log b)*(log b/log p) by field_simp]
    rw [mul_pow]
    field_simp
  rw [heq]
  apply (div_le_div_of_nonneg_right (interval_psi_bound A a b n hn hA ha hab hr) hrp.le).trans_eq
  unfold psi primitive test
  simp only [pow_succ]
  field_simp
  ring

theorem prime_moment_one_le (A b : ℝ) (hA : 0 < A) (hb : 2 ≤ b) (hr : 2 ≤ A/log b) :
    (∑ p ∈ SieveSmallWeights.pool b, (log b/log p)*test A p*
      (PrimeEulerMass.weight p/primeEuler b)) ≤
      exp (1-A/log b)*((A/log b+1)/(A/log b)^2 +
        (PrimeEulerDimensionOne.errorConstant/log b)*
          (1+2*((A/log b)^2+2*(A/log b)+2)/(A/log b)^3)) := by
  simpa only [PrimeEulerExponentialBound.intervalPrimes_two_eq_pool, poly, pow_one,
    show (1:ℕ)+1=2 by rfl, show (1:ℕ)+2=3 by rfl] using
      interval_moment_le A 2 b 1 (by norm_num) hA (by norm_num) hb hr

theorem prime_moment_two_le (A b : ℝ) (hA : 0 < A) (hb : 2 ≤ b) (hr : 2 ≤ A/log b) :
    (∑ p ∈ SieveSmallWeights.pool b, (log b/log p)^2*test A p*
      (PrimeEulerMass.weight p/primeEuler b)) ≤
      exp (1-A/log b)*(((A/log b)^2+2*(A/log b)+2)/(A/log b)^3 +
        (PrimeEulerDimensionOne.errorConstant/log b)*
          (1+2*((A/log b)^3+3*(A/log b)^2+6*(A/log b)+6)/(A/log b)^4)) := by
  simpa only [PrimeEulerExponentialBound.intervalPrimes_two_eq_pool, poly,
    show (2:ℕ)+1=3 by rfl, show (2:ℕ)+2=4 by rfl] using
      interval_moment_le A 2 b 2 (by norm_num) hA (by norm_num) hb hr

run_cmd do
  for decl in [``poly_hasDerivAt, ``poly_nonneg, ``psi_hasDerivAt, ``psi_nonneg,
      ``psiD_nonneg, ``psi_continuousOn, ``psiD_continuousOn, ``primitive_hasDerivAt,
      ``primitive_cube_hasDerivAt, ``primitive_nonneg, ``kernel_intervalIntegrable,
      ``integral_kernel_two_le, ``integral_kernel_three_le, ``interval_psi_bound,
      ``interval_moment_le, ``prime_moment_one_le, ``prime_moment_two_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL PRIME EULER EXPONENTIAL MOMENTS: STANDARD AXIOMS ONLY"

end PrimeEulerExponentialMoments
end
